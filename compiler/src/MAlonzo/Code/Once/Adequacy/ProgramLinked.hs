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
import qualified MAlonzo.Code.Once.Adequacy.FunBundle
import qualified MAlonzo.Code.Once.Adequacy.TelePosition
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.Denotation.Realize
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Ref
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Module
import qualified MAlonzo.Code.Once.Surface.Context
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
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_spliceWith_48 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_spliceWith_48 v2 v4 v5 v6 v7 v8 v9 v10 v11
du_spliceWith_48 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
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
                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_420 (coe v6))
                                (coe v0)
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_418 (coe v6)))
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
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_428
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_438
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_448
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_456
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_464
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_474
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_484
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_504 v9 v12 v13 v14 v15
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_528 v9 v11 v13 v14 v15 v16 v17 v18
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_548 v12 v13 v14 v15
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_568 v12 v13 v14 v15
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_586 v13
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_600 v11 v12
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'ana'45'check_616 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v16 v17 v18
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_132 v19 v20
                             -> coe
                                  d_realize'45'refs_228 (coe v0) (coe v15)
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v16)
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                        (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                     (coe
                                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v19)
                                        (coe v16)))
                                  (coe v3) (coe v13)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_628 v7 v10 v11
        -> coe
             d_realize'45'refs'45'i_240 (coe v0) (coe v1) (coe v7) (coe v3)
             (coe v10)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_648 v11 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v18 v19 v20
                      -> coe
                           d_realize'45'refs_228
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_432 (coe v0)
                              (coe v16) (coe v18))
                           (coe v17) (coe v20)
                           (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v3)
                           (coe v15)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_664 v10 v11 v12 v13
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_674 v8 v9 v10
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_686 v7 v9 v10
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_698 v9 v10
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_710 v9 v10
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_720 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs_228 (coe v0) (coe v11)
                       (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_734 v8 v9 v10 v15
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
        -> erased
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_80 v8 v10
        -> erased
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'own_88 v10
        -> erased
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_96 v11
        -> erased
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_112 v8 v9 v10 v11 v15
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v10)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe MAlonzo.Code.Once.Type.Rigid.du_ground'45'kinded_458))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_122 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v11 v12
               -> coe
                    d_realize'45'refs_228 (coe v0) (coe v11) (coe v2) (coe v3)
                    (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_138 v10 v11 v12 v13
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_146 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> coe
                    d_realize'45'refs'45'i_240 (coe v0) (coe v10)
                    (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v3) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_158
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_178 v9 v11 v12 v13 v14 v15
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
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_432 (coe v0)
                          (coe v16) (coe v9))
                       (coe v18) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v11 v13)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_208 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
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
                             MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_432 (coe v0)
                             (coe v23) (coe v11))
                          (coe v24) (coe v2)
                          (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v14 v17)
                          (coe v20))
                       (coe
                          d_realize'45'refs'45'i_240
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_432 (coe v0)
                             (coe v25) (coe v12))
                          (coe v26) (coe v2)
                          (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v18)
                          (coe v21)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_222 v9 v10 v12 v13
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_236 v9 v10 v12 v13
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_250 v9 v10 v12 v13
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_264 v9 v10 v12 v13
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_278 v9 v10 v12 v13
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_288 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v11) (coe v2) (coe v8)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_300 v8 v9 v10
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_312 v7 v9 v10
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_322 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v11) (coe v7) (coe v8)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_334 v7 v9 v10
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_346 v7 v9 v10
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_358 v7 v9 v10 v12
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_370 v7 v9 v10 v12
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_388 v8 v10 v11 v12 v14 v15
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_404 v8 v10 v11 v13 v14
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_420 v8 v10 v11 v13 v14
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_752 v10 v13 v15 v16 v17
        -> coe
             d_realize'45'refs'45'i_240 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v10)
                (coe
                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                (coe v3))
             (coe v5) (coe v15)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_776 v12 v13 v14 v15 v16 v17 v22 v23 v24 v25
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v17)))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v24))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_794 v12 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v17 v18
               -> coe
                    d_realize'45'refs'45'i_240
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_432 (coe v0)
                       (coe v17) (coe v2))
                    (coe v18) (coe v3)
                    (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v12 v5)
                    (coe v16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_814 v11 v14 v15 v16 v17
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_822
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_832
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_842
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_850
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_856
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_876 v14 v15 v16 v17
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_896 v14 v15 v16 v17
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_910 v13 v14
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
d_L_584 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_L_584 = erased
-- Once.Adequacy.ProgramLinked._.as-case
d_as'45'case_612 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_as'45'case_612 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16 v17
  = du_as'45'case_612 v16 v17
du_as'45'case_612 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> AgdaAny) -> AgdaAny
du_as'45'case_612 v0 v1
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
d_rp'45'case_666 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_rp'45'case_666 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14
  = du_rp'45'case_666 v3 v4 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_rp'45'case_666 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
du_rp'45'case_666 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
        -> case coe v11 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
               -> case coe v13 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                      -> coe
                           du_as'45'case_612
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6220
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
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
d_nothing'8802'just_690 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_nothing'8802'just_690 = erased
-- Once.Adequacy.ProgramLinked._.resolve-refs
d_resolve'45'refs_732 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_resolve'45'refs_732 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12
                      v13
  = du_resolve'45'refs_732 v2 v3 v4 v6 v7 v8 v9 v11 v12 v13
du_resolve'45'refs_732 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
du_resolve'45'refs_732 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v12
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v13 v19
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
               -> coe
                    du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
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
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v16)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v7))
                       (coe v17) (coe v19))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
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
                              du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
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
                              du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
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
                              du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6) (coe v18) (coe v16) (coe v20))
                           (coe
                              du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6) (coe v19) (coe v17) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_90 v14 v15
        -> coe
             du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
             (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v7) (coe v14))
             (coe v15) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_102 v13 v15
        -> coe
             du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
             (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v13) (coe v7))
             (coe v15) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_114 v15
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'43'__126 v16 v17
               -> coe
                    du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v16) (coe v15) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_126 v15
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'43'__126 v16 v17
               -> coe
                    du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
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
                              du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6)
                              (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v17) (coe v18))
                              (coe v20) (coe v23))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                 (coe addInt (coe (1 :: Integer)) (coe v5))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v6)
                                    (coe v17))
                                 (coe v7) (coe v21) (coe v25))
                              (coe
                                 du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
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
             du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v14)
             (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_180 v12 v13 v14 v15 v17 v18
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v15) (coe v17) (coe v19))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
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
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sub_214 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_mul_224 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_234 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_244 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_254 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Float_136)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_272 v13
        -> coe
             du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13)
             (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_div_282 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_292 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_neg_300 v13
        -> coe
             du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13)
             (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_lt_310 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_le_320 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_gt_330 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ge_340 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_eq_350 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ne_360 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14)
                       (coe v16))
                    (coe
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v15)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v13 v15 v16
        -> coe
             du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v13) (coe v16) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380 v13 v14 -> coe v9
      MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v13 -> coe v9
      MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v12
        -> coe
             du_rp'45'case_666 (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
             (coe v7) (coe v5) (coe v6)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPolyPrefix_144
                (coe v0) (coe v12))
             erased (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_closed_406 v13
        -> coe
             du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
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
                       du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
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
                                     du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v6)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v15)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v24))
                                        (coe v22))
                                     (coe v18) (coe v25))
                                  (coe
                                     du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3)
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
                                            du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2)
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
                                            du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2)
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
                                            du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2)
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
                                            du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2)
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
                                  du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3)
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
                                  du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3)
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
      MAlonzo.Code.Once.Surface.Syntax.C_ana_532 v17 v18
        -> case coe v7 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
               -> case coe v21 of
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v22 v23
                      -> coe
                           du_resolve'45'refs_732 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v5) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v19)
                              (coe
                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v22) (coe v19)))
                           (coe v18) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.dc-linked
d_dc'45'linked_1284 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_dc'45'linked_1284 ~v0 ~v1 v2 ~v3 v4 = du_dc'45'linked_1284 v2 v4
du_dc'45'linked_1284 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_dc'45'linked_1284 v0 v1
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
d_ref'45'entry_1402 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
d_ref'45'entry_1402 ~v0 ~v1 v2 v3 v4
  = du_ref'45'entry_1402 v2 v3 v4
du_ref'45'entry_1402 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_ref'45'entry_1402 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_846
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_846
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_846
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__126 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_846
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> coe
                    seq (coe v6)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                          (coe
                             MAlonzo.Code.Once.Compile.d_irFunOf_846
                             (coe
                                MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                                (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                                (coe v2))))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_846
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_846
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_846
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_846
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_rigid_138 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_846
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
                      (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.RefLinked-mono
d_RefLinked'45'mono_1550 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_RefLinked'45'mono_1550 ~v0 ~v1 ~v2 v3 v4 v5
  = du_RefLinked'45'mono_1550 v3 v4 v5
du_RefLinked'45'mono_1550 ::
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_RefLinked'45'mono_1550 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linked'45'mono_88
      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
      (coe
         MAlonzo.Code.Once.IR.Ref.d_refIR_8 (coe v2)
         (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v1)))
-- Once.Adequacy.ProgramLinked.LInv
d_LInv_1564 a0 a1 a2 = ()
data T_LInv_1564
  = C_constructor_1632 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Type.T_Type_108 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748)
                       (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Type.T_Type_108 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748)
                       MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                       (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Type.T_Type_108 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny)
                       ((MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                         MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
                        MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34)
-- Once.Adequacy.ProgramLinked.LInv.irf
d_irf_1602 ::
  T_LInv_1564 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
d_irf_1602 v0
  = case coe v0 of
      C_constructor_1632 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.irs
d_irs_1604 ::
  T_LInv_1564 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
d_irs_1604 v0
  = case coe v0 of
      C_constructor_1632 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.iself
d_iself_1606 ::
  T_LInv_1564 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_iself_1606 v0
  = case coe v0 of
      C_constructor_1632 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.imp-ok
d_imp'45'ok_1612 ::
  T_LInv_1564 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_imp'45'ok_1612 v0
  = case coe v0 of
      C_constructor_1632 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.tel-ok
d_tel'45'ok_1620 ::
  T_LInv_1564 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_tel'45'ok_1620 v0
  = case coe v0 of
      C_constructor_1632 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.ent-ok
d_ent'45'ok_1624 ::
  T_LInv_1564 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ent'45'ok_1624 v0
  = case coe v0 of
      C_constructor_1632 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.sig-ok
d_sig'45'ok_1630 ::
  T_LInv_1564 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_sig'45'ok_1630 v0
  = case coe v0 of
      C_constructor_1632 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.SpliceOK-mono
d_SpliceOK'45'mono_1652 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_SpliceOK'45'mono_1652 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 v9 v10 v11
                        v12 v13 v14 v15 v16 v17
  = du_SpliceOK'45'mono_1652
      v3 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
du_SpliceOK'45'mono_1652 ::
  (MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
du_SpliceOK'45'mono_1652 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13
  = coe
      MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_Refs'45'map_760
      (coe (\ v14 v15 v16 -> v16))
      (coe du_RefLinked'45'mono_1550 (coe v0))
      (coe du_RefLinked'45'mono_1550 (coe v0)) (coe v3)
      (coe
         du_spliceWith_48 (coe v7) (coe v1) (coe v10) (coe v11) (coe v2)
         (coe v3) (coe v1 v2) (coe v6)
         (coe
            MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6220
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
               (coe v1 v2) (coe v7))
            (coe v6) (coe v3)))
      (coe v4 v5 v6 v7 v8 v9 v10 v11 v12 v13)
-- Once.Adequacy.ProgramLinked.ents-cons
d_ents'45'cons_1706 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ents'45'cons_1706 ~v0 v1 v2 v3 v4
  = du_ents'45'cons_1706 v1 v2 v3 v4
du_ents'45'cons_1706 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ents'45'cons_1706 v0 v1 v2 v3
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
d_imp'45'cons_1736 ::
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
d_imp'45'cons_1736 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_imp'45'cons_1736 v3 v5 v6 v7 v8 v9 v10
du_imp'45'cons_1736 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_imp'45'cons_1736 v0 v1 v2 v3 v4 v5 v6
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
                          du_RefLinked'45'mono_1550
                          (coe
                             MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'cons_18
                             (coe v1))
                          v4 v5 (coe v3 v4 v5 v6))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ProgramLinked.sig-cons
d_sig'45'cons_1816 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_sig'45'cons_1816 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 v8
  = du_sig'45'cons_1816 v2 v4 v5 v6 v7 v8
du_sig'45'cons_1816 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_sig'45'cons_1816 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v6 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                 (coe v3)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then coe seq (coe v8) (coe v1)
                else coe seq (coe v8) (coe v2 v3 v4 v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ProgramLinked.linv-sig
d_linv'45'sig_1880 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  T_LInv_1564 -> T_LInv_1564
d_linv'45'sig_1880 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_linv'45'sig_1880 v3 v5 v6 v7
du_linv'45'sig_1880 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  T_LInv_1564 -> T_LInv_1564
du_linv'45'sig_1880 v0 v1 v2 v3
  = coe
      C_constructor_1632 (coe d_irf_1602 (coe v3))
      (coe
         MAlonzo.Code.Once.Adequacy.TelePosition.du_irf'45'cons_28 (coe v0)
         (coe v1) (coe d_irs_1604 (coe v3)))
      (coe d_iself_1606 (coe v3)) (coe d_imp'45'ok_1612 (coe v3))
      (coe d_tel'45'ok_1620 (coe v3)) (coe d_ent'45'ok_1624 (coe v3))
      (coe
         du_sig'45'cons_1816 (coe v0) (coe v2)
         (coe d_sig'45'ok_1630 (coe v3)))
-- Once.Adequacy.ProgramLinked.linv-entry
d_linv'45'entry_1908 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  AgdaAny -> T_LInv_1564 -> T_LInv_1564
d_linv'45'entry_1908 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_linv'45'entry_1908 v2 v3 v4 v5 v6 v7 v8
du_linv'45'entry_1908 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  AgdaAny -> T_LInv_1564 -> T_LInv_1564
du_linv'45'entry_1908 v0 v1 v2 v3 v4 v5 v6
  = coe
      C_constructor_1632
      (coe
         MAlonzo.Code.Once.Adequacy.TelePosition.du_irf'45'cons_28 (coe v1)
         (coe v4) (coe d_irf_1602 (coe v6)))
      (coe d_irs_1604 (coe v6)) (coe d_iself_1606 (coe v6))
      (coe
         du_imp'45'cons_1736 (coe v1)
         (coe du_e_1932 (coe v1) (coe v2) (coe v3))
         (coe du_ref'45'entry_1402 (coe v1) (coe v2) (coe v3))
         (coe d_imp'45'ok_1612 (coe v6)))
      (coe
         (\ v7 v8 v9 v10 v11 ->
            coe
              du_SpliceOK'45'mono_1652
              (coe
                 MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'cons_18
                 (coe du_e_1932 (coe v1) (coe v2) (coe v3)))
              (coe v7) (coe v9) (coe v10)
              (coe d_tel'45'ok_1620 v6 v7 v8 v9 v10 v11)))
      (coe
         du_ents'45'cons_1706 (coe du_e_1932 (coe v1) (coe v2) (coe v3))
         (coe v0) (coe v5) (coe d_ent'45'ok_1624 (coe v6)))
      (coe d_sig'45'ok_1630 (coe v6))
-- Once.Adequacy.ProgramLinked._.e
d_e_1932 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748 ->
  AgdaAny ->
  T_LInv_1564 -> MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_1932 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 = du_e_1932 v3 v4 v5
du_e_1932 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_1932 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Compile.d_irFunOf_846
      (coe
         MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
         (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v0)) (coe v1)
         (coe v2))
-- Once.Adequacy.ProgramLinked.body-linked
d_body'45'linked_1960 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1564 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_body'45'linked_1960 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
                      ~v12
  = du_body'45'linked_1960 v0 v1 v2 v3 v4 v5 v6
du_body'45'linked_1960 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1564 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> AgdaAny
du_body'45'linked_1960 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ElaborateLinked.d_elaborate'45'linked_2520
      (coe v0) (coe v2) (coe MAlonzo.Code.Once.IR.C_Heap_8)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
            (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1))
            (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))))
      (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62) (coe v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_3954
         (coe v5) (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))
         (coe
            MAlonzo.Code.Once.Compile.d_declImps_406
            (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v1)))
         (coe du_uf_1986 (coe v1) (coe v4) (coe v5)) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
                     (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1))
                     (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))))
               (coe (0 :: Integer))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_420
                  (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1)))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_418
                  (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1))))
            (coe v6) (coe v5)
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
            (coe du_D'8242'_1984 (coe v1) (coe v5) (coe v6))))
      (coe
         du_resolve'45'refs_732
         (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))
         (coe
            MAlonzo.Code.Once.Compile.d_declImps_406
            (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v1)))
         (coe
            d_tel'45'ok_1620 v3
            (MAlonzo.Code.Once.Compile.d_declImps_406
               (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v1)))
            (d_iself_1606 (coe v3)))
         (coe du_uf_1986 (coe v1) (coe v4) (coe v5)) (coe (0 :: Integer))
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
               (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))))
         (coe v5)
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
                     (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1))
                     (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))))
               (coe (0 :: Integer))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_420
                  (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1)))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_418
                  (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1))))
            (coe v6) (coe v5)
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
            (coe du_D'8242'_1984 (coe v1) (coe v5) (coe v6)))
         (coe
            MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_Refs'45'map_760
            (coe
               (\ v7 ->
                  coe
                    d_sig'45'ok_1630 v3
                    (MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v7))))
            (coe d_imp'45'ok_1612 (coe v3)) (coe (\ v7 v8 v9 -> v9)) (coe v5)
            (coe
               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
                        (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1))
                        (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))))
                  (coe (0 :: Integer))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_420
                     (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1)))
                  (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_418
                     (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1))))
               (coe v6) (coe v5)
               (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
               (coe du_D'8242'_1984 (coe v1) (coe v5) (coe v6)))
            (coe
               d_realize'45'refs_228
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
                        (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1))
                        (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))))
                  (coe (0 :: Integer))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_420
                     (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1)))
                  (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v1))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_418
                     (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1))))
               (coe v6) (coe v5)
               (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
               (coe du_D'8242'_1984 (coe v1) (coe v5) (coe v6)))))
-- Once.Adequacy.ProgramLinked._.D′
d_D'8242'_1984 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1564 ->
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
d_D'8242'_1984 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_D'8242'_1984 v1 v5 v6
du_D'8242'_1984 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_D'8242'_1984 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of_334
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6220
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
            (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v0))
            (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v0)))
         (coe v2) (coe v1))
-- Once.Adequacy.ProgramLinked._.uf
d_uf_1986 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1564 ->
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
d_uf_1986 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_uf_1986 v1 v4 v5
du_uf_1986 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_uf_1986 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v0))
-- Once.Adequacy.ProgramLinked.splice-at
d_splice'45'at_2030 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_splice'45'at_2030 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 v18
  = du_splice'45'at_2030 v16 v18
du_splice'45'at_2030 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_splice'45'at_2030 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v4 v5 v6 v7
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.linv-poly
d_linv'45'poly_2062 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 -> T_LInv_1564
d_linv'45'poly_2062 ~v0 v1 ~v2 v3 v4
  = du_linv'45'poly_2062 v1 v3 v4
du_linv'45'poly_2062 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 -> T_LInv_1564
du_linv'45'poly_2062 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         (\ v3 v4 v5 ->
            coe
              C_constructor_1632 (coe d_irf_1602 (coe v5))
              (coe d_irs_1604 (coe v5))
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                 (coe
                    MAlonzo.Code.Once.Adequacy.TelePosition.du_iself'45'step_138
                    (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v0))
                    (coe
                       MAlonzo.Code.Once.Adequacy.TelePosition.du_'43''43''8315''691'_170
                       (coe
                          MAlonzo.Code.Data.List.Base.du_map_22
                          (coe (\ v6 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
                          (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v0)))
                       (coe v4))
                    (coe d_iself_1606 (coe v5))))
              (coe d_imp'45'ok_1612 (coe v5))
              (\ v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 ->
                 coe
                   du_tel'8242'_2156 (coe v0) (coe v1) (coe v5) v6 v7 v8 v9 v10 v11
                   v12 v13 v16 v17 v18 v19)
              (coe d_ent'45'ok_1624 (coe v5)) (coe d_sig'45'ok_1630 (coe v5))))
-- Once.Adequacy.ProgramLinked._.y
d_y_2082 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_y_2082 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_y_2082 v3
du_y_2082 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_y_2082 v0 = coe MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v0)
-- Once.Adequacy.ProgramLinked._.scT
d_scT_2084 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 -> MAlonzo.Code.Once.Type.T_PolyType_254
d_scT_2084 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_scT_2084 v3
du_scT_2084 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Type.T_PolyType_254
du_scT_2084 v0
  = coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v0)
-- Once.Adequacy.ProgramLinked._.bd
d_bd_2086 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_bd_2086 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_bd_2086 v3
du_bd_2086 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
du_bd_2086 v0
  = coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v0)
-- Once.Adequacy.ProgramLinked._.polys
d_polys_2088 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polys_2088 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_polys_2088 v1
du_polys_2088 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_polys_2088 v0
  = coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v0)
-- Once.Adequacy.ProgramLinked._.imps
d_imps_2090 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imps_2090 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_imps_2090 v1
du_imps_2090 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_imps_2090 v0
  = coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v0)
-- Once.Adequacy.ProgramLinked._.top
d_top_2092 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 -> MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412
d_top_2092 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_top_2092 v1
du_top_2092 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412
du_top_2092 v0 = coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v0)
-- Once.Adequacy.ProgramLinked._.head-ok
d_head'45'ok_2108 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6 -> AgdaAny
d_head'45'ok_2108 ~v0 v1 ~v2 v3 ~v4 ~v5 v6 v7 ~v8 v9 v10 ~v11 ~v12
                  v13 v14 ~v15 ~v16
  = du_head'45'ok_2108 v1 v3 v6 v7 v9 v10 v13 v14
du_head'45'ok_2108 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  T_LInv_1564 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Integer -> AgdaAny
du_head'45'ok_2108 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_splice'45'at_2030 (coe du_cr_2134 (coe v0) (coe v1) (coe v5))
      (coe
         du_resolve'45'refs_732 (coe du_polys_2088 (coe v0)) (coe v3)
         (coe d_tel'45'ok_1620 v2 v3 v4) (coe v6) (coe v7)
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
               (coe du_top_2092 (coe v0)) (coe du_polys_2088 (coe v0))))
         (coe v5)
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
                     (coe du_top_2092 (coe v0)) (coe du_polys_2088 (coe v0))))
               (coe (0 :: Integer))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_420
                  (coe du_top_2092 (coe v0)))
               (coe du_polys_2088 (coe v0))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_418
                  (coe du_top_2092 (coe v0))))
            (coe du_bd_2086 (coe v1)) (coe v5)
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
            (coe du_w_2138 (coe v0) (coe v1) (coe v5)))
         (coe
            MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_Refs'45'map_760
            (coe
               (\ v8 ->
                  coe
                    d_sig'45'ok_1630 v2
                    (MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v8))))
            (coe d_imp'45'ok_1612 (coe v2)) (coe (\ v8 v9 v10 -> v10)) (coe v5)
            (coe
               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
                        (coe du_top_2092 (coe v0)) (coe du_polys_2088 (coe v0))))
                  (coe (0 :: Integer))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_420
                     (coe du_top_2092 (coe v0)))
                  (coe du_polys_2088 (coe v0))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_418
                     (coe du_top_2092 (coe v0))))
               (coe du_bd_2086 (coe v1)) (coe v5)
               (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
               (coe du_w_2138 (coe v0) (coe v1) (coe v5)))
            (coe
               d_realize'45'refs_228
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
                        (coe du_top_2092 (coe v0)) (coe du_polys_2088 (coe v0))))
                  (coe (0 :: Integer))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_420
                     (coe du_top_2092 (coe v0)))
                  (coe du_polys_2088 (coe v0))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_418
                     (coe du_top_2092 (coe v0))))
               (coe du_bd_2086 (coe v1)) (coe v5)
               (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
               (coe du_w_2138 (coe v0) (coe v1) (coe v5)))))
-- Once.Adequacy.ProgramLinked._._.D-A
d_D'45'A_2132 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_D'45'A_2132 ~v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
              ~v13 ~v14 ~v15 ~v16
  = du_D'45'A_2132 v1 v3 v4 v6 v11
du_D'45'A_2132 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  T_LInv_1564 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_D'45'A_2132 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.TypeCheck.Instance.du_inst'45'at_24
      (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_402 (coe v0))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v1))
      (coe du_scT_2084 (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_irf_1602 (coe v3)) (coe d_irs_1604 (coe v3)))
      (coe v2) (coe v4)
-- Once.Adequacy.ProgramLinked._._.cr
d_cr_2134 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_cr_2134 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16
  = du_cr_2134 v1 v3 v10
du_cr_2134 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cr_2134 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6220
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_426
         (coe du_top_2092 (coe v0)) (coe du_polys_2088 (coe v0)))
      (coe du_bd_2086 (coe v1)) (coe v2)
-- Once.Adequacy.ProgramLinked._._.ce
d_ce_2136 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_ce_2136 = erased
-- Once.Adequacy.ProgramLinked._._.w
d_w_2138 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_w_2138 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16
  = du_w_2138 v1 v3 v10
du_w_2138 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_w_2138 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of_334
      (coe du_cr_2134 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.ProgramLinked._.tel′
d_tel'8242'_2156 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1564 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
d_tel'8242'_2156 ~v0 v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 ~v15 ~v16 v17 v18 v19 v20
  = du_tel'8242'_2156
      v1 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v17 v18 v19 v20
du_tel'8242'_2156 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  T_LInv_1564 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_412) ->
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
du_tel'8242'_2156 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v17 v18
        -> let v19
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v19 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe du_y_2082 (coe v1)))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                        (coe du_y_2082 (coe v1)) (coe v5)) in
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
                                           du_head'45'ok_2108 (coe v0) (coe v1) (coe v2) (coe v3)
                                           (coe v18) (coe v6) (coe v11) (coe v12))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       else coe
                              seq (coe v21)
                              (coe
                                 d_tel'45'ok_1620 v2 v3 v18 v5 v6 v7 v8 v9 v10 erased erased v11 v12
                                 v13 v14)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.link-walk
d_link'45'walk_2300 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1564 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_link'45'walk_2300 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Module.C_'91''93'_54
        -> coe seq (coe v4) (coe d_ent'45'ok_1624 (coe v6))
      MAlonzo.Code.Once.Spec.Module.C_ffi_64 v11 v15 v16 v17 v18
        -> case coe v2 of
             (:) v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v21
                      -> case coe v4 of
                           MAlonzo.Code.Once.Adequacy.FunBundle.C_bffi_32 v24 v26 v27 v28 v34
                             -> coe
                                  d_link'45'walk_2300 (coe v0)
                                  (coe
                                     MAlonzo.Code.Once.Compile.C_cscope_392
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v21))
                                           (coe v11))
                                        (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v1)))
                                     (coe MAlonzo.Code.Once.Compile.d_cimps_388 (coe v1))
                                     (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v1)))
                                  (coe v20) (coe v18) (coe v34) (coe v5)
                                  (coe
                                     du_linv'45'sig_1880
                                     (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v21))
                                     (coe v17)
                                     (coe
                                        v8
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v21))
                                           (coe v11))
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                           erased))
                                     (coe v6))
                                  (coe
                                     MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'sig_292
                                     (coe v7))
                                  (coe
                                     (\ v35 v36 ->
                                        coe
                                          v8 v35
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                             v36)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Module.C_mono_76 v11 v13 v16 v17 v18
        -> case coe v2 of
             (:) v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v21
                      -> case coe v21 of
                           MAlonzo.Code.Once.Parser.C_mkFunInfo_114 v22 v23 v24 v25
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Adequacy.FunBundle.C_bcons_64 v29 v30 v31 v32 v33 v34 v37 v41
                                    -> coe
                                         seq (coe v30)
                                         (coe
                                            d_link'45'walk_2300 (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.Compile.C_cscope_392
                                               (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v1))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v22) (coe v11))
                                                  (coe
                                                     MAlonzo.Code.Once.Compile.d_cimps_388
                                                     (coe v1)))
                                               (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v1)))
                                            (coe v20) (coe v18) (coe v41)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Program.C_irFun_24
                                                  (coe
                                                     MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe v22)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                                  (coe
                                                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                        (coe
                                                           MAlonzo.Code.Once.Compile.d_directCallIR_20
                                                           (coe v11) (coe v34))))
                                                  (coe
                                                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              MAlonzo.Code.Once.Compile.d_directCallIR_20
                                                              (coe v11) (coe v34)))))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           MAlonzo.Code.Once.Compile.d_directCallIR_20
                                                           (coe v11) (coe v34)))))
                                               (coe v5))
                                            (coe
                                               du_linv'45'entry_1908 (coe v5) (coe v22) (coe v11)
                                               (coe v34) (coe v16)
                                               (coe
                                                  du_dc'45'linked_1284 (coe v11)
                                                  (coe
                                                     du_body'45'linked_1960 (coe v0) (coe v1)
                                                     (coe v5) (coe v6) (coe v22) (coe v11)
                                                     (coe v24)))
                                               (coe v6))
                                            (coe
                                               MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'fun_272
                                               (coe v20) (coe v7))
                                            (coe v8))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Module.C_poly_86 v12 v13 v14
        -> case coe v2 of
             (:) v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v17
                      -> case coe v4 of
                           MAlonzo.Code.Once.Adequacy.FunBundle.C_bpoly_82 v21 v22 v23 v24 v26
                             -> coe
                                  d_link'45'walk_2300 (coe v0)
                                  (coe
                                     MAlonzo.Code.Once.Compile.C_cscope_392
                                     (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v1))
                                     (coe
                                        MAlonzo.Code.Once.Spec.Module.d_imps_16
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                           (coe v1)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                           (coe MAlonzo.Code.Once.Compile.d_ctop_396 (coe v1)))
                                        (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v1))))
                                  (coe v16) (coe v14) (coe v26) (coe v5)
                                  (coe
                                     du_linv'45'poly_2062
                                     (coe
                                        MAlonzo.Code.Once.Compile.C_cscope_392
                                        (coe MAlonzo.Code.Once.Compile.d_csig_386 (coe v1))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Module.d_imps_16
                                           (coe
                                              MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_270
                                              (coe v1)))
                                        (coe MAlonzo.Code.Once.Compile.d_ctele_390 (coe v1)))
                                     v17 v12 v13
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'head_260
                                        (coe v7))
                                     v6)
                                  (coe
                                     MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'poly_304
                                     (coe v1) (coe v16) (coe v7))
                                  (coe v8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.main-linked
d_main'45'linked_2546 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  AgdaAny -> AgdaAny
d_main'45'linked_2546 ~v0 v1 v2 ~v3 v4
  = du_main'45'linked_2546 v1 v2 v4
du_main'45'linked_2546 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  AgdaAny -> AgdaAny
du_main'45'linked_2546 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bffi_32 v5 v7 v8 v9 v15
        -> case coe v0 of
             (:) v16 v17
               -> coe du_main'45'linked_2546 (coe v17) (coe v15) (coe v2)
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
                                        MAlonzo.Code.Once.Compile.d_tableOf'45'go_856
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'8594'compiled_332
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
                      -> coe du_main'45'linked_2546 (coe v20) (coe v18) (coe v21)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bpoly_82 v6 v7 v8 v9 v11
        -> case coe v0 of
             (:) v12 v13
               -> coe du_main'45'linked_2546 (coe v13) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked._.e
d_e_2586 ::
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
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
d_e_2586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16
  = du_e_2586 v8
du_e_2586 ::
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_2586 v0
  = coe
      MAlonzo.Code.Once.Compile.d_irFunOf_846
      (coe
         MAlonzo.Code.Once.Compile.C_mkCompiledFun_252
         (coe
            MAlonzo.Code.Once.CanonicalName.d_bare_12
            (coe ("main" :: Data.Text.Text)))
         (coe MAlonzo.Code.Once.Spec.Module.d_EffUU_188) (coe v0))
-- Once.Adequacy.ProgramLinked.linv₀
d_linv'8320'_2590 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_LInv_1564
d_linv'8320'_2590 ~v0 = du_linv'8320'_2590
du_linv'8320'_2590 :: T_LInv_1564
du_linv'8320'_2590
  = coe
      C_constructor_1632 erased erased
      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      erased
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 v7 v8 ->
            coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      erased
-- Once.Adequacy.ProgramLinked._.no-poly
d_no'45'poly_2600 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'poly_2600 = erased
-- Once.Adequacy.ProgramLinked.typed-ef
d_typed'45'ef_2620 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50
d_typed'45'ef_2620 ~v0 ~v1 v2 ~v3 ~v4 = du_typed'45'ef_2620 v2
du_typed'45'ef_2620 ::
  AgdaAny -> MAlonzo.Code.Once.Spec.Module.T_ModTele_50
du_typed'45'ef_2620 v0 = coe v0
-- Once.Adequacy.ProgramLinked.moduleToProgram-linked
d_moduleToProgram'45'linked_2630 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToProgram'45'linked_2630 v0 ~v1 ~v2
  = du_moduleToProgram'45'linked_2630 v0
du_moduleToProgram'45'linked_2630 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_moduleToProgram'45'linked_2630 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Adequacy.FunBundle.du_node'45'ef_1094
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
                                 du_main'45'linked_2546 (coe v2) (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'45'find'45'exists_1012
                                    (coe v2) (coe v6)))
                              (coe
                                 d_link'45'walk_2300
                                 (coe MAlonzo.Code.Once.Spec.Module.d_moduleSig_172 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.Compile.C_cscope_392
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_cimps_388
                                       (coe MAlonzo.Code.Once.Compile.d_emptyCScope_394))
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                 (coe v2) (coe du_mt'8320'_2666 (coe v0)) (coe v6)
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 (coe du_linv'8320'_2590)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.TelePosition.du_entries'45'distinct_412
                                       (coe v0) (coe v2))
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.TelePosition.d_none'45'in'45'empty_424
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_map_22
                                          (coe
                                             MAlonzo.Code.Once.Adequacy.TelePosition.d_entryName_64)
                                          (coe v2))))
                                 (coe (\ v8 v9 -> v9)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ProgramLinked._.T
d_T_2660 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_T_2660 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 = du_T_2660 v3 v5
du_T_2660 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
du_T_2660 v0 v1
  = coe
      MAlonzo.Code.Once.Compile.d_tableOf'45'go_856
      (coe
         MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'8594'compiled_332
         (coe v0) (coe v1))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.Adequacy.ProgramLinked._.bf
d_bf_2662 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bf_2662 = erased
-- Once.Adequacy.ProgramLinked._.ir≡
d_ir'8801'_2664 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ir'8801'_2664 = erased
-- Once.Adequacy.ProgramLinked._.mt₀
d_mt'8320'_2666 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50
d_mt'8320'_2666 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_mt'8320'_2666 v0
du_mt'8320'_2666 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Spec.Module.T_ModTele_50
du_mt'8320'_2666 v0
  = coe
      MAlonzo.Code.Once.Adequacy.AcceptSound.du_moduleToIR'45'typed_606
      (coe v0)
-- Once.Adequacy.ProgramLinked._.u
d_u_2670 ::
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
d_u_2670 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_u_2670 v8
du_u_2670 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_u_2670 v0 = coe v0
