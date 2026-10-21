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
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Properties
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
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Module
import qualified MAlonzo.Code.Once.Lang.Name
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Instance
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.ProgramLinked.ImpRef
d_ImpRef_8 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_ImpRef_8 = erased
-- Once.Adequacy.ProgramLinked.FFIRef
d_FFIRef_16 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_FFIRef_16 = erased
-- Once.Adequacy.ProgramLinked.PolyRef
d_PolyRef_24 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_PolyRef_24 = erased
-- Once.Adequacy.ProgramLinked.spliceWith
d_spliceWith_48 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_spliceWith_48 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_spliceWith_48 v2 v4 v5 v6 v7 v8 v9 v10 v11
du_spliceWith_48 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
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
                       MAlonzo.Code.Once.Surface.Syntax.C_closed_410
                       (coe
                          MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExprWF_3364
                          (coe v5) (coe v0) (coe v1) (coe v2) (coe v3)
                          (coe
                             MAlonzo.Code.Once.Denotation.Realize.d_realize_20
                             (coe
                                MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                (coe (0 :: Integer))
                                (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                                (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8)
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340 (coe v6))
                                (coe v0)
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338 (coe v6)))
                             (coe v7) (coe v5)
                             (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v10))))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_114 v11
               -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.SpliceOK
d_SpliceOK_80 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_SpliceOK_80 = erased
-- Once.Adequacy.ProgramLinked.Refs-substA
d_Refs'45'substA_130 ::
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()) ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_Refs'45'substA_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_Refs'45'substA_130 v10
du_Refs'45'substA_130 :: AgdaAny -> AgdaAny
du_Refs'45'substA_130 v0 = coe v0
-- Once.Adequacy.ProgramLinked.Refs-substF
d_Refs'45'substF_160 ::
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()) ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  (MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
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
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> ()
d_RR_214 = erased
-- Once.Adequacy.ProgramLinked.realize-refs
d_realize'45'refs_228 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  AgdaAny
d_realize'45'refs_228 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'check_432 v8
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'check_444 v9
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'check_456 v9
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'morph'45'check_466 v8
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'morph'45'check_476 v8
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'morph'45'check_488 v9
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'morph'45'check_500 v9
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'g_520 v9 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            d_realize'45'refs_228 (coe v0) (coe v19)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v24))
                                               (coe v22))
                                            (coe v12) (coe v15))
                                         (coe
                                            d_realize'45'refs'45'd_256 (coe v0) (coe v17) (coe v20)
                                            (coe v9) (coe v24) (coe v13) (coe v14))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'f_544 v9 v11 v13 v14 v15 v16 v17 v18
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v23 v24 v25
                             -> case coe v24 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v26 v27
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            d_realize'45'refs'45'i_240 (coe v0) (coe v22)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v13))
                                               (coe v11))
                                            (coe v14) (coe v16))
                                         (coe
                                            d_realize'45'refs_228 (coe v0) (coe v20)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v23)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v27))
                                               (coe v9))
                                            (coe v15) (coe v18))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case'45'copair'45'check_564 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Lang.Type.C__'43'__26 v23 v24
                                    -> case coe v21 of
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v25 v26
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   d_realize'45'refs_228 (coe v0) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v23)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v26))
                                                      (coe v22))
                                                   (coe v12) (coe v14))
                                                (coe
                                                   d_realize'45'refs_228 (coe v0) (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v24)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v26))
                                                      (coe v22))
                                                   (coe v13) (coe v15))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'morph'45'check_584 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                                    -> case coe v22 of
                                         MAlonzo.Code.Once.Lang.Type.C__'42'__24 v25 v26
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   d_realize'45'refs_228 (coe v0) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v20)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v24))
                                                      (coe v25))
                                                   (coe v12) (coe v14))
                                                (coe
                                                   d_realize'45'refs_228 (coe v0) (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v20)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v24))
                                                      (coe v26))
                                                   (coe v13) (coe v15))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'curry'45'check_604 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
                      -> case coe v19 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                                    -> coe
                                         d_realize'45'refs_228 (coe v0) (coe v16)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v17)
                                               (coe v20))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v24))
                                            (coe v22))
                                         (coe v3) (coe v14)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'cata'45'check_620 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
                      -> case coe v16 of
                           MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v19
                             -> case coe v17 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v20 v21
                                    -> coe
                                         d_realize'45'refs_228 (coe v0) (coe v15)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                               (coe v19) (coe v18))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v21))
                                            (coe v18))
                                         (coe v10) (coe v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'ana'45'check_640 v11 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
                      -> case coe v20 of
                           MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v21 v22
                             -> coe
                                  d_realize'45'refs_228 (coe v0) (coe v17)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v18)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v22)))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v21)
                                        (coe v18)))
                                  (coe v11) (coe v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'loop'45'check_652 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
                      -> coe
                           d_realize'45'refs_228 (coe v0) (coe v12)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                              (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v15) (coe v13)))
                           (coe v9) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_664 v7 v10 v11
        -> coe
             d_realize'45'refs'45'i_240 (coe v0) (coe v1) (coe v7) (coe v3)
             (coe v10)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'lam_686 v11 v14 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v17 v18
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                      -> coe
                           d_realize'45'refs_228
                           (coe
                              MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
                              (coe v17) (coe v19))
                           (coe v18) (coe v21)
                           (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v11 v3) (coe v16)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'lit'45'check_702 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v16 v17
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'In'45'app'45'check_712 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              d_realize'45'refs_228 (coe v0) (coe v12)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v13)
                                 (coe v2))
                              (coe v8) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'check_724 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'42'__24
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'app'45'check_736 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              d_realize'45'refs_228 (coe v0) (coe v12) (coe v13) (coe v9)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'app'45'check_748 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              d_realize'45'refs_228 (coe v0) (coe v12) (coe v14) (coe v9)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'app'45'check_758 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs_228 (coe v0) (coe v11)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v8) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate_772 v8 v9 v10 v15
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
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny
d_realize'45'refs'45'i_240 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'int_30
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'float_42
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit_46
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62 v9
        -> coe seq (coe v9) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_70 v8 v10
        -> erased
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_78 -> erased
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_86 v11 -> erased
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_102 v8 v9 v10 v11 v15
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v10)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe MAlonzo.Code.Once.Type.Rigid.du_ground'45'kinded_350))
      MAlonzo.Code.Once.Lang.Typing.C_t'45'annot_112 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_58 v11 v12
               -> coe
                    d_realize'45'refs_228 (coe v0) (coe v11) (coe v2) (coe v3)
                    (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_128 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v16 v17
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg_136 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_62 v10
               -> coe
                    d_realize'45'refs'45'i_240 (coe v0) (coe v10)
                    (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v3) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg'45'float_148
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_t'45'let_168 v9 v11 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v16 v17 v18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v17) (coe v9) (coe v12)
                       (coe v14))
                    (coe
                       d_realize'45'refs'45'i_240
                       (coe
                          MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
                          (coe v16) (coe v9))
                       (coe v18) (coe v2)
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v11 v13)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case_202 v11 v12 v13 v14 v16 v17 v18 v19 v20 v21 v22 v23 v24
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v25 v26 v27 v28 v29
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v25)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v11) (coe v12))
                       (coe v18) (coe v21))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240
                          (coe
                             MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
                             (coe v26) (coe v11))
                          (coe v27) (coe v13)
                          (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v16 v19)
                          (coe v22))
                       (coe
                          d_realize'45'refs'45'i_240
                          (coe
                             MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
                             (coe v28) (coe v12))
                          (coe v29) (coe v14)
                          (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v17 v20)
                          (coe v23)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_216 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9) (coe v12))
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10) (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float_230 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v9) (coe v12))
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v10) (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'il_244 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9) (coe v12))
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v10) (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'ir_258 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v9) (coe v12))
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10) (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_272 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v14 v15 v16
               -> coe
                    seq (coe v14)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v15)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9) (coe v12))
                       (coe
                          d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                          (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10) (coe v13)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_282 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v11) (coe v2) (coe v8)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'app_294 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v8))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'app_306 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v7) (coe v2))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_316 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v11) (coe v7) (coe v8)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_328 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v12)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'42'__24
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v2))
                          (coe v7))
                       (coe v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_344 v7 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
                      -> case coe v16 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v18 v19
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                  (coe
                                     d_realize'45'refs'45'i_240 (coe v0) (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                           (coe v7)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe v19))
                                           (coe v17))
                                        (coe v7))
                                     (coe v9) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_356 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v7)
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42))
                       (coe v9) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_368 v7 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v14)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v7)
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44))
                       (coe v9) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app_386 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v8)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v10)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v2))
                       (coe v11) (coe v14))
                    (coe
                       d_realize'45'refs_228 (coe v0) (coe v17) (coe v8) (coe v12)
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_406 v8 v10 v11 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v22 v23
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_realize'45'refs'45'i_240 (coe v0) (coe v17)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v8)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v23))
                                        (coe v21))
                                     (coe v10) (coe v15))
                                  (coe
                                     d_realize'45'refs_228 (coe v0) (coe v18) (coe v8) (coe v11)
                                     (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_422 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       d_realize'45'refs'45'd_256 (coe v0) (coe v15) (coe v8) (coe v2)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) (coe v10)
                       (coe v14))
                    (coe
                       d_realize'45'refs'45'i_240 (coe v0) (coe v16) (coe v8) (coe v11)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.realize-refs-d
d_realize'45'refs'45'd_256 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  AgdaAny
d_realize'45'refs'45'd_256 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_790 v10 v13 v15 v16 v17
        -> coe
             d_realize'45'refs'45'i_240 (coe v0) (coe v1)
             (coe
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v10)
                (coe
                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v13))
                (coe v3))
             (coe v5) (coe v15)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_814 v12 v13 v14 v15 v16 v17 v22 v23 v24 v25
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16) (coe v17)))
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v24))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_834 v12 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v17 v18
               -> coe
                    d_realize'45'refs'45'i_240
                    (coe
                       MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132 (coe v0)
                       (coe v17) (coe v2))
                    (coe v18) (coe v3)
                    (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v12 v5) (coe v16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_854 v11 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
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
      MAlonzo.Code.Once.Lang.Typing.C_d'45'id_864 v10
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_876 v11
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_888 v11
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_898 v10
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_906 v9
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Lang.Typing.C_d'45'case_930 v12 v13 v16 v17 v18 v19 v20
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v23 v24
                      -> case coe v2 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v25 v26
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_realize'45'refs'45'd_256 (coe v0) (coe v24) (coe v25)
                                     (coe v12) (coe v4) (coe v16) (coe v18))
                                  (coe
                                     d_realize'45'refs'45'd_256 (coe v0) (coe v22) (coe v26)
                                     (coe v13) (coe v4) (coe v17) (coe v19))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_950 v14 v15 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
                      -> case coe v3 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v22 v23
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
      MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_966 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v18
                      -> coe
                           d_realize'45'refs'45'i_240 (coe v0) (coe v17)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v18)
                                 (coe v3))
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))
                              (coe v3))
                           (coe v12) (coe v15)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked._.L
d_L_578 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_L_578 = erased
-- Once.Adequacy.ProgramLinked._.as-case
d_as'45'case_606 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> AgdaAny) -> AgdaAny
d_as'45'case_606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13 ~v14 ~v15 v16 v17
  = du_as'45'case_606 v16 v17
du_as'45'case_606 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Induction.WellFounded.T_Acc_42 -> AgdaAny) -> AgdaAny
du_as'45'case_606 v0 v1
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
d_rp'45'case_660 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_rp'45'case_660 ~v0 ~v1 ~v2 v3 v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14
  = du_rp'45'case_660 v3 v4 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_rp'45'case_660 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_rp'45'case_660 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v8 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
        -> case coe v11 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
               -> case coe v13 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                      -> coe
                           du_as'45'case_606
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
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
d_nothing'8802'just_684 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_684 = erased
-- Once.Adequacy.ProgramLinked._.resolve-refs
d_resolve'45'refs_726 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
d_resolve'45'refs_726 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 v8 v9 ~v10 v11 v12
                      v13
  = du_resolve'45'refs_726 v2 v3 v4 v6 v7 v8 v9 v11 v12 v13
du_resolve'45'refs_726 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 -> AgdaAny -> AgdaAny
du_resolve'45'refs_726 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v12
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v13 v19
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
               -> coe
                    du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe addInt (coe (1 :: Integer)) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v6) (coe v20))
                    (coe v22) (coe v19) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_50 v12 v13 v14 v16 v17 v18
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v16)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v7))
                       (coe v17) (coe v19))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v14) (coe v18) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v12 v13 v14 v17 v18 v19
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v6)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v14)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v24))
                                        (coe v22))
                                     (coe v18) (coe v25))
                                  (coe
                                     du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v6) (coe v14) (coe v19) (coe v26))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v12 v13 v16 v17
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v18 v19
               -> case coe v9 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6) (coe v18) (coe v16) (coe v20))
                           (coe
                              du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6) (coe v19) (coe v17) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_94 v14 v15
        -> coe
             du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
             (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v7) (coe v14))
             (coe v15) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_106 v13 v15
        -> coe
             du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6)
             (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v13) (coe v7))
             (coe v15) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_118 v15
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v16 v17
               -> coe
                    du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v16) (coe v15) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_130 v15
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v16 v17
               -> coe
                    du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6) (coe v17) (coe v15) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_152 v12 v13 v14 v15 v16 v17 v18 v20 v21 v22
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
               -> case coe v24 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6)
                              (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v17) (coe v18))
                              (coe v20) (coe v23))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                 (coe addInt (coe (1 :: Integer)) (coe v5))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v6) (coe v17))
                                 (coe v7) (coe v21) (coe v25))
                              (coe
                                 du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                 (coe addInt (coe (1 :: Integer)) (coe v5))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v6) (coe v18))
                                 (coe v7) (coe v22) (coe v26)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_unit_158
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_168 v14
        -> coe
             du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
             (coe v14) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_184 v12 v13 v14 v15 v17 v18
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v15) (coe v17) (coe v19))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe addInt (coe (1 :: Integer)) (coe v5))
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v6) (coe v15))
                       (coe v7) (coe v18) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_190 v12
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v12
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v13
        -> coe
             du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe v13) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_div_286 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v13
        -> coe
             du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
             (coe v13) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_le_324 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v12 v13 v14 v15
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v14) (coe v16))
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                       (coe v15) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v13 v15 v16
        -> coe
             du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v13) (coe v16) (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v13 v14 -> coe v9
      MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v13 -> coe v9
      MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v12
        -> coe
             du_rp'45'case_660 (coe v1) (coe v2) (coe v3) (coe v4) (coe v12)
             (coe v7) (coe v5) (coe v6)
             (coe
                MAlonzo.Code.Once.Lang.Typing.Scope.d_lookupPolyPrefix_68 (coe v0)
                (coe v12))
             erased (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_closed_410 v13
        -> coe
             du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
             (coe (0 :: Integer))
             (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8) (coe v7) (coe v13)
             (coe v9)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422 v15
        -> coe v9
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v12 v13 v15 v16
        -> case coe v9 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                    (coe
                       du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v5) (coe v6) (coe v13) (coe v16) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v12 v13 v15 v18 v19
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                      -> case coe v9 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v6)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v24))
                                        (coe v22))
                                     (coe v18) (coe v25))
                                  (coe
                                     du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v4) (coe v5) (coe v6)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v20)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v24))
                                        (coe v15))
                                     (coe v19) (coe v26))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v12 v13 v18 v19
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
               -> case coe v20 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v23 v24
                      -> case coe v21 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v25 v26
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2)
                                            (coe v3) (coe v4) (coe v5) (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v23)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v26))
                                               (coe v22))
                                            (coe v18) (coe v27))
                                         (coe
                                            du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2)
                                            (coe v3) (coe v4) (coe v5) (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v24)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v26))
                                               (coe v22))
                                            (coe v19) (coe v28))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v12 v13 v18 v19
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
               -> case coe v21 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v23 v24
                      -> case coe v22 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v25 v26
                             -> case coe v9 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2)
                                            (coe v3) (coe v4) (coe v5) (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v20)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v24))
                                               (coe v25))
                                            (coe v18) (coe v27))
                                         (coe
                                            du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2)
                                            (coe v3) (coe v4) (coe v5) (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v20)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v24))
                                               (coe v26))
                                            (coe v19) (coe v28))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_506 v18
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
               -> case coe v21 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v22 v23 v24
                      -> case coe v23 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v25 v26
                             -> coe
                                  du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3)
                                  (coe v4) (coe v5) (coe v6)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v19) (coe v22))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v26))
                                     (coe v24))
                                  (coe v18) (coe v9)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v12 v16 v17
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v21
                      -> case coe v19 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v22 v23
                             -> coe
                                  du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3)
                                  (coe v4) (coe v5) (coe v6)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v21)
                                        (coe v20))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v23))
                                     (coe v20))
                                  (coe v17) (coe v9)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v12 v17 v18
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
               -> case coe v21 of
                    MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v22 v23
                      -> coe
                           du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                           (coe v5) (coe v6)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v19)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v23)))
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v22)
                                 (coe v19)))
                           (coe v18) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_loop_548 v12 v15
        -> case coe v7 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> coe
                    du_resolve'45'refs_726 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v16)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                       (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v18) (coe v16)))
                    (coe v15) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.dc-linked
d_dc'45'linked_1288 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_dc'45'linked_1288 ~v0 ~v1 v2 ~v3 v4 = du_dc'45'linked_1288 v2 v4
du_dc'45'linked_1288 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
du_dc'45'linked_1288 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Void_22 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v2 v3 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v2 v3 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v5 v6
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
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v2 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v2 v3 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_Float_36 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.ref-entry
d_ref'45'entry_1406 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
d_ref'45'entry_1406 ~v0 ~v1 v2 v3 v4
  = du_ref'45'entry_1406 v2 v3 v4
du_ref'45'entry_1406 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_ref'45'entry_1406 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_1300
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                      (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_1300
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                      (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_1300
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                      (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_1300
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                      (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 v6 v7
               -> coe
                    seq (coe v6)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                          (coe
                             MAlonzo.Code.Once.Compile.d_irFunOf_1300
                             (coe
                                MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                                (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v0)) (coe v1)
                                (coe v2))))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_1300
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                      (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_1300
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                      (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_1300
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                      (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_1300
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                      (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                (coe
                   MAlonzo.Code.Once.Compile.d_irFunOf_1300
                   (coe
                      MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                      (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v0)) (coe v1)
                      (coe v2))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.RefLinked-mono
d_RefLinked'45'mono_1554 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_RefLinked'45'mono_1554 ~v0 ~v1 ~v2 v3 v4 v5
  = du_RefLinked'45'mono_1554 v3 v4 v5
du_RefLinked'45'mono_1554 ::
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
du_RefLinked'45'mono_1554 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linked'45'mono_88
      (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
      (coe
         MAlonzo.Code.Once.IR.Ref.d_refIR_8 (coe v2)
         (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v1)))
-- Once.Adequacy.ProgramLinked.LInv
d_LInv_1568 a0 a1 a2 = ()
data T_LInv_1568
  = C_constructor_1636 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68)
                       (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68)
                       MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                       (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny)
                       ((MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                         MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
                        MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
                        MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                        MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                        MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
                        MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
                        [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
                        [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                        Integer ->
                        Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny)
                       MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                       (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                        MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                        MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                        MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34)
-- Once.Adequacy.ProgramLinked.LInv.irf
d_irf_1606 ::
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
d_irf_1606 v0
  = case coe v0 of
      C_constructor_1636 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.irs
d_irs_1608 ::
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
d_irs_1608 v0
  = case coe v0 of
      C_constructor_1636 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.iself
d_iself_1610 ::
  T_LInv_1568 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_iself_1610 v0
  = case coe v0 of
      C_constructor_1636 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.imp-ok
d_imp'45'ok_1616 ::
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_imp'45'ok_1616 v0
  = case coe v0 of
      C_constructor_1636 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.tel-ok
d_tel'45'ok_1624 ::
  T_LInv_1568 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny
d_tel'45'ok_1624 v0
  = case coe v0 of
      C_constructor_1636 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.ent-ok
d_ent'45'ok_1628 ::
  T_LInv_1568 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ent'45'ok_1628 v0
  = case coe v0 of
      C_constructor_1636 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.LInv.sig-ok
d_sig'45'ok_1634 ::
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_sig'45'ok_1634 v0
  = case coe v0 of
      C_constructor_1636 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.SpliceOK-mono
d_SpliceOK'45'mono_1656 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny
d_SpliceOK'45'mono_1656 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 v9 v10 v11
                        v12 v13 v14 v15 v16 v17
  = du_SpliceOK'45'mono_1656
      v3 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17
du_SpliceOK'45'mono_1656 ::
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
   MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Integer ->
   Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny
du_SpliceOK'45'mono_1656 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                         v13
  = coe
      MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_Refs'45'map_778
      (coe (\ v14 v15 v16 -> v16))
      (coe du_RefLinked'45'mono_1554 (coe v0))
      (coe du_RefLinked'45'mono_1554 (coe v0)) (coe v3)
      (coe
         du_spliceWith_48 (coe v7) (coe v1) (coe v10) (coe v11) (coe v2)
         (coe v3) (coe v1 v2) (coe v6)
         (coe
            MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6302
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
               (coe v1 v2) (coe v7))
            (coe v6) (coe v3)))
      (coe v4 v5 v6 v7 v8 v9 v10 v11 v12 v13)
-- Once.Adequacy.ProgramLinked.ents-cons
d_ents'45'cons_1710 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_ents'45'cons_1710 ~v0 v1 v2 v3 v4
  = du_ents'45'cons_1710 v1 v2 v3 v4
du_ents'45'cons_1710 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_ents'45'cons_1710 v0 v1 v2 v3
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
d_imp'45'cons_1740 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_imp'45'cons_1740 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_imp'45'cons_1740 v3 v5 v6 v7 v8 v9 v10
du_imp'45'cons_1740 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_imp'45'cons_1740 v0 v1 v2 v3 v4 v5 v6
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
                          du_RefLinked'45'mono_1554
                          (coe
                             MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'cons_18
                             (coe v1))
                          v4 v5 (coe v3 v4 v5 v6))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ProgramLinked.imp-defs
d_imp'45'defs_1826 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_imp'45'defs_1826 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_imp'45'defs_1826 v1 v4 v6 v7 v8 v9 v10 v11
du_imp'45'defs_1826 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_imp'45'defs_1826 v0 v1 v2 v3 v4 v5 v6 v7
  = if coe v0
      then coe
             du_RefLinked'45'mono_1554
             (coe
                MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'cons_18
                (coe v2))
             v5 v6 (coe v4 v5 v6 v7)
      else coe
             du_imp'45'cons_1740 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6) erased
-- Once.Adequacy.ProgramLinked.sig-cons
d_sig'45'cons_1872 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_sig'45'cons_1872 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 v8
  = du_sig'45'cons_1872 v2 v4 v5 v6 v7 v8
du_sig'45'cons_1872 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_sig'45'cons_1872 v0 v1 v2 v3 v4 v5
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
d_linv'45'sig_1936 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  T_LInv_1568 -> T_LInv_1568
d_linv'45'sig_1936 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_linv'45'sig_1936 v3 v5 v6 v7
du_linv'45'sig_1936 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  T_LInv_1568 -> T_LInv_1568
du_linv'45'sig_1936 v0 v1 v2 v3
  = coe
      C_constructor_1636 (coe d_irf_1606 (coe v3))
      (coe
         MAlonzo.Code.Once.Adequacy.TelePosition.du_irf'45'cons_28 (coe v0)
         (coe v1) (coe d_irs_1608 (coe v3)))
      (coe d_iself_1610 (coe v3)) (coe d_imp'45'ok_1616 (coe v3))
      (coe d_tel'45'ok_1624 (coe v3)) (coe d_ent'45'ok_1628 (coe v3))
      (coe
         du_sig'45'cons_1872 (coe v0) (coe v2)
         (coe d_sig'45'ok_1634 (coe v3)))
-- Once.Adequacy.ProgramLinked.linv-entry
d_linv'45'entry_1964 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny -> T_LInv_1568 -> T_LInv_1568
d_linv'45'entry_1964 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_linv'45'entry_1964 v2 v3 v4 v5 v6 v7 v8
du_linv'45'entry_1964 ::
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny -> T_LInv_1568 -> T_LInv_1568
du_linv'45'entry_1964 v0 v1 v2 v3 v4 v5 v6
  = coe
      C_constructor_1636
      (coe
         MAlonzo.Code.Once.Adequacy.TelePosition.du_irf'45'defs_72
         (coe
            MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v1)
            (coe ("main" :: Data.Text.Text)))
         (coe v1) (coe v4) (coe d_irf_1606 (coe v6)))
      (coe d_irs_1608 (coe v6)) (coe d_iself_1610 (coe v6))
      (coe
         du_imp'45'defs_1826
         (coe
            MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v1)
            (coe ("main" :: Data.Text.Text)))
         (coe v1) (coe du_e_1988 (coe v1) (coe v2) (coe v3))
         (coe du_ref'45'entry_1406 (coe v1) (coe v2) (coe v3))
         (coe d_imp'45'ok_1616 (coe v6)))
      (coe
         (\ v7 v8 v9 v10 v11 ->
            coe
              du_SpliceOK'45'mono_1656
              (coe
                 MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'cons_18
                 (coe du_e_1988 (coe v1) (coe v2) (coe v3)))
              (coe v7) (coe v9) (coe v10)
              (coe d_tel'45'ok_1624 v6 v7 v8 v9 v10 v11)))
      (coe
         du_ents'45'cons_1710 (coe du_e_1988 (coe v1) (coe v2) (coe v3))
         (coe v0) (coe v5) (coe d_ent'45'ok_1628 (coe v6)))
      (coe d_sig'45'ok_1634 (coe v6))
-- Once.Adequacy.ProgramLinked._.e
d_e_1988 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  AgdaAny ->
  T_LInv_1568 -> MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e_1988 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 = du_e_1988 v3 v4 v5
du_e_1988 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e_1988 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Compile.d_irFunOf_1300
      (coe
         MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
         (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v0)) (coe v1)
         (coe v2))
-- Once.Adequacy.ProgramLinked.body-linked
d_body'45'linked_2016 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_body'45'linked_2016 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
                      ~v12
  = du_body'45'linked_2016 v0 v1 v2 v3 v4 v5 v6
du_body'45'linked_2016 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 -> AgdaAny
du_body'45'linked_2016 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ElaborateLinked.d_elaborate'45'linked_2616
      (coe v0) (coe v2) (coe MAlonzo.Code.Once.IR.C_Heap_8)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
            (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
      (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
         (coe v5) (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
         (coe
            MAlonzo.Code.Once.Compile.d_declImps_650
            (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
         (coe du_uf_2042 (coe v1) (coe v4) (coe v5)) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                     (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                  (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1)))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                  (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))))
            (coe v6) (coe v5)
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
            (coe du_D'8242'_2040 (coe v1) (coe v5) (coe v6))))
      (coe
         du_resolve'45'refs_726
         (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
         (coe
            MAlonzo.Code.Once.Compile.d_declImps_650
            (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
         (coe
            d_tel'45'ok_1624 v3
            (MAlonzo.Code.Once.Compile.d_declImps_650
               (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
            (d_iself_1610 (coe v3)))
         (coe du_uf_2042 (coe v1) (coe v4) (coe v5)) (coe (0 :: Integer))
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
               (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
         (coe v5)
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                     (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                  (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1)))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                  (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))))
            (coe v6) (coe v5)
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
            (coe du_D'8242'_2040 (coe v1) (coe v5) (coe v6)))
         (coe
            MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_Refs'45'map_778
            (coe
               (\ v7 ->
                  coe
                    d_sig'45'ok_1634 v3
                    (MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v7))))
            (coe d_imp'45'ok_1616 (coe v3)) (coe (\ v7 v8 v9 -> v9)) (coe v5)
            (coe
               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe
                     MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                        (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                        (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1)))
                  (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))))
               (coe v6) (coe v5)
               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
               (coe du_D'8242'_2040 (coe v1) (coe v5) (coe v6)))
            (coe
               d_realize'45'refs_228
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe
                     MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                        (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                        (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1)))
                  (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))))
               (coe v6) (coe v5)
               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
               (coe du_D'8242'_2040 (coe v1) (coe v5) (coe v6)))))
-- Once.Adequacy.ProgramLinked._.D′
d_D'8242'_2040 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_D'8242'_2040 ~v0 v1 ~v2 ~v3 ~v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_D'8242'_2040 v1 v5 v6
du_D'8242'_2040 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_D'8242'_2040 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of_388
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6302
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0))
            (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0)))
         (coe v2) (coe v1))
-- Once.Adequacy.ProgramLinked._.uf
d_uf_2042 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_uf_2042 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_uf_2042 v1 v4 v5
du_uf_2042 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_uf_2042 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.Compile.d_cimps_632 (coe v0))
-- Once.Adequacy.ProgramLinked.body-linkedI
d_body'45'linkedI_2070 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_body'45'linkedI_2070 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
                       ~v12
  = du_body'45'linkedI_2070 v0 v1 v2 v3 v4 v5 v6
du_body'45'linkedI_2070 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 -> AgdaAny
du_body'45'linkedI_2070 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Adequacy.ElaborateLinked.d_elaborate'45'linked_2616
      (coe v0) (coe v2) (coe MAlonzo.Code.Once.IR.C_Heap_8)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
            (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
      (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48) (coe v5)
      (coe
         MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_resolveExpr_4060
         (coe v5) (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
         (coe
            MAlonzo.Code.Once.Compile.d_declImps_650
            (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
         (coe du_uf_2096 (coe v1) (coe v4) (coe v5)) (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
            (coe
               MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                     (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                  (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1)))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                  (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))))
            (coe v6) (coe v5)
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
            (coe du_D'8242'_2094 (coe v1) (coe v6))))
      (coe
         du_resolve'45'refs_726
         (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
         (coe
            MAlonzo.Code.Once.Compile.d_declImps_650
            (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
         (coe
            d_tel'45'ok_1624 v3
            (MAlonzo.Code.Once.Compile.d_declImps_650
               (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
            (d_iself_1610 (coe v3)))
         (coe du_uf_2096 (coe v1) (coe v4) (coe v5)) (coe (0 :: Integer))
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
               (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
         (coe v5)
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
            (coe
               MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                     (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                  (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1)))
               (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                  (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))))
            (coe v6) (coe v5)
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
            (coe du_D'8242'_2094 (coe v1) (coe v6)))
         (coe
            MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_Refs'45'map_778
            (coe
               (\ v7 ->
                  coe
                    d_sig'45'ok_1634 v3
                    (MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v7))))
            (coe d_imp'45'ok_1616 (coe v3)) (coe (\ v7 v8 v9 -> v9)) (coe v5)
            (coe
               MAlonzo.Code.Once.Denotation.Realize.d_realize'45'infer_30
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe
                     MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                        (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                        (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1)))
                  (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))))
               (coe v6) (coe v5)
               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
               (coe du_D'8242'_2094 (coe v1) (coe v6)))
            (coe
               d_realize'45'refs'45'i_240
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe
                     MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                        (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))
                        (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1)))
                  (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v1))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                     (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1))))
               (coe v6) (coe v5)
               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
               (coe du_D'8242'_2094 (coe v1) (coe v6)))))
-- Once.Adequacy.ProgramLinked._.D′
d_D'8242'_2094 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
d_D'8242'_2094 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_D'8242'_2094 v1 v6
du_D'8242'_2094 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10
du_D'8242'_2094 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of'45'i_408
      (coe
         MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_6294
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
            (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0))
            (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0)))
         (coe v1))
-- Once.Adequacy.ProgramLinked._.uf
d_uf_2096 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_uf_2096 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
  = du_uf_2096 v1 v4 v5
du_uf_2096 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_uf_2096 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      (coe MAlonzo.Code.Once.Compile.d_cimps_632 (coe v0))
-- Once.Adequacy.ProgramLinked.body-linkedM
d_body'45'linkedM_2126 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1568 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_body'45'linkedM_2126 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9 ~v10 ~v11
                       ~v12 ~v13 ~v14
  = du_body'45'linkedM_2126 v0 v1 v2 v3 v4 v5 v6 v7 v9
du_body'45'linkedM_2126 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1568 ->
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 -> AgdaAny
du_body'45'linkedM_2126 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
        -> coe
             seq (coe v8)
             (coe
                du_body'45'linked_2016 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                (coe v6) (coe v7))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             seq (coe v8)
             (coe
                du_body'45'linkedI_2070 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v5) (coe v6) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.splice-at
d_splice'45'at_2182 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_splice'45'at_2182 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 ~v14 ~v15 v16 ~v17 v18
  = du_splice'45'at_2182 v16 v18
du_splice'45'at_2182 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_splice'45'at_2182 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_112 v4 v5 v6 v7
               -> coe seq (coe v4) (coe v1)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.linv-poly
d_linv'45'poly_2214 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 -> T_LInv_1568
d_linv'45'poly_2214 ~v0 v1 ~v2 v3 v4
  = du_linv'45'poly_2214 v1 v3 v4
du_linv'45'poly_2214 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 -> T_LInv_1568
du_linv'45'poly_2214 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         (\ v3 v4 v5 ->
            coe
              C_constructor_1636 (coe d_irf_1606 (coe v5))
              (coe d_irs_1608 (coe v5))
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                 (coe
                    MAlonzo.Code.Once.Adequacy.TelePosition.du_iself'45'step_168
                    (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v0))
                    (coe
                       MAlonzo.Code.Once.Adequacy.TelePosition.du_'43''43''8315''691'_200
                       (coe
                          MAlonzo.Code.Data.List.Base.du_map_22
                          (coe (\ v6 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
                          (coe MAlonzo.Code.Once.Compile.d_cimps_632 (coe v0)))
                       (coe v4))
                    (coe d_iself_1610 (coe v5))))
              (coe d_imp'45'ok_1616 (coe v5))
              (\ v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 ->
                 coe
                   du_tel'8242'_2306 (coe v0) (coe v1) (coe v5) v6 v7 v8 v9 v10 v11
                   v12 v13 v16 v17 v18 v19)
              (coe d_ent'45'ok_1628 (coe v5)) (coe d_sig'45'ok_1634 (coe v5))))
-- Once.Adequacy.ProgramLinked._.y
d_y_2234 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_y_2234 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_y_2234 v3
du_y_2234 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_y_2234 v0 = coe MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v0)
-- Once.Adequacy.ProgramLinked._.scT
d_scT_2236 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 -> MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
d_scT_2236 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_scT_2236 v3
du_scT_2236 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10
du_scT_2236 v0
  = coe MAlonzo.Code.Once.Parser.d_pfunType_126 (coe v0)
-- Once.Adequacy.ProgramLinked._.bd
d_bd_2238 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 -> MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34
d_bd_2238 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 = du_bd_2238 v3
du_bd_2238 ::
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34
du_bd_2238 v0
  = coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v0)
-- Once.Adequacy.ProgramLinked._.polys
d_polys_2240 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polys_2240 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_polys_2240 v1
du_polys_2240 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_polys_2240 v0
  = coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0)
-- Once.Adequacy.ProgramLinked._.imps
d_imps_2242 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imps_2242 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_imps_2242 v1
du_imps_2242 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_imps_2242 v0
  = coe MAlonzo.Code.Once.Compile.d_cimps_632 (coe v0)
-- Once.Adequacy.ProgramLinked._.top
d_top_2244 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 -> MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332
d_top_2244 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_top_2244 v1
du_top_2244 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332
du_top_2244 v0 = coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0)
-- Once.Adequacy.ProgramLinked._.head-ok
d_head'45'ok_2260 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny
d_head'45'ok_2260 ~v0 v1 ~v2 v3 ~v4 ~v5 v6 v7 ~v8 v9 v10 ~v11 ~v12
                  v13 v14 ~v15 ~v16
  = du_head'45'ok_2260 v1 v3 v6 v7 v9 v10 v13 v14
du_head'45'ok_2260 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  T_LInv_1568 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Integer -> AgdaAny
du_head'45'ok_2260 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_splice'45'at_2182 (coe du_cr_2286 (coe v0) (coe v1) (coe v5))
      (coe
         du_resolve'45'refs_726 (coe du_polys_2240 (coe v0)) (coe v3)
         (coe d_tel'45'ok_1624 v2 v3 v4) (coe v6) (coe v7)
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
               (coe du_top_2244 (coe v0)) (coe du_polys_2240 (coe v0))))
         (coe v5)
         (coe
            MAlonzo.Code.Once.Denotation.Realize.d_realize_20
            (coe
               MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
               (coe (0 :: Integer))
               (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                     (coe du_top_2244 (coe v0)) (coe du_polys_2240 (coe v0))))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                  (coe du_top_2244 (coe v0)))
               (coe du_polys_2240 (coe v0))
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                  (coe du_top_2244 (coe v0))))
            (coe du_bd_2238 (coe v1)) (coe v5)
            (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
            (coe du_w_2290 (coe v0) (coe v1) (coe v5)))
         (coe
            MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_Refs'45'map_778
            (coe
               (\ v8 ->
                  coe
                    d_sig'45'ok_1634 v2
                    (MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v8))))
            (coe d_imp'45'ok_1616 (coe v2)) (coe (\ v8 v9 v10 -> v10)) (coe v5)
            (coe
               MAlonzo.Code.Once.Denotation.Realize.d_realize_20
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe
                     MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                        (coe du_top_2244 (coe v0)) (coe du_polys_2240 (coe v0))))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                     (coe du_top_2244 (coe v0)))
                  (coe du_polys_2240 (coe v0))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                     (coe du_top_2244 (coe v0))))
               (coe du_bd_2238 (coe v1)) (coe v5)
               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
               (coe du_w_2290 (coe v0) (coe v1) (coe v5)))
            (coe
               d_realize'45'refs_228
               (coe
                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                  (coe (0 :: Integer))
                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_6)
                  (coe
                     MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
                        (coe du_top_2244 (coe v0)) (coe du_polys_2240 (coe v0))))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tdefs_340
                     (coe du_top_2244 (coe v0)))
                  (coe du_polys_2240 (coe v0))
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_tsig_338
                     (coe du_top_2244 (coe v0))))
               (coe du_bd_2238 (coe v1)) (coe v5)
               (coe MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)
               (coe du_w_2290 (coe v0) (coe v1) (coe v5)))))
-- Once.Adequacy.ProgramLinked._._.D-A
d_D'45'A_2284 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_D'45'A_2284 ~v0 v1 ~v2 v3 v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
              ~v13 ~v14 ~v15 ~v16
  = du_D'45'A_2284 v1 v3 v4 v6 v11
du_D'45'A_2284 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_D'45'A_2284 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.TypeCheck.Instance.du_inst'45'at_24
      (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v0))
      (coe MAlonzo.Code.Once.Compile.d_cpolys_646 (coe v0))
      (coe MAlonzo.Code.Once.Parser.d_pfunBody_128 (coe v1))
      (coe du_scT_2236 (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe d_irf_1606 (coe v3)) (coe d_irs_1608 (coe v3)))
      (coe v2) (coe v4)
-- Once.Adequacy.ProgramLinked._._.cr
d_cr_2286 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cr_2286 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
          ~v14 ~v15 ~v16
  = du_cr_2286 v1 v3 v10
du_cr_2286 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cr_2286 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_6302
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_346
         (coe du_top_2244 (coe v0)) (coe du_polys_2240 (coe v0)))
      (coe du_bd_2238 (coe v1)) (coe v2)
-- Once.Adequacy.ProgramLinked._._.ce
d_ce_2288 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ce_2288 = erased
-- Once.Adequacy.ProgramLinked._._.w
d_w_2290 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
d_w_2290 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16
  = du_w_2290 v1 v3 v10
du_w_2290 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16
du_w_2290 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Adequacy.TelePosition.du_sound'45'of_388
      (coe du_cr_2286 (coe v0) (coe v1) (coe v2))
-- Once.Adequacy.ProgramLinked._.tel′
d_tel'8242'_2306 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  T_LInv_1568 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny
d_tel'8242'_2306 ~v0 v1 ~v2 v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12 v13
                 v14 ~v15 ~v16 v17 v18 v19 v20
  = du_tel'8242'_2306
      v1 v3 v6 v7 v8 v9 v10 v11 v12 v13 v14 v17 v18 v19 v20
du_tel'8242'_2306 ::
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_PolyFunInfo_116 ->
  T_LInv_1568 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6 -> AgdaAny
du_tel'8242'_2306 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v17 v18
        -> let v19
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v19 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe du_y_2234 (coe v1)))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                        (coe du_y_2234 (coe v1)) (coe v5)) in
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
                                           du_head'45'ok_2260 (coe v0) (coe v1) (coe v2) (coe v3)
                                           (coe v18) (coe v6) (coe v11) (coe v12))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       else coe
                              seq (coe v21)
                              (coe
                                 d_tel'45'ok_1624 v2 v3 v18 v5 v6 v7 v8 v9 v10 erased erased v11 v12
                                 v13 v14)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.link-walk
d_link'45'walk_2450 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  T_LInv_1568 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_link'45'walk_2450 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Module.C_'91''93'_74
        -> coe seq (coe v4) (coe d_ent'45'ok_1628 (coe v6))
      MAlonzo.Code.Once.Lang.Module.C_ffi_84 v11 v15 v16 v17 v18
        -> case coe v2 of
             (:) v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v21
                      -> case coe v4 of
                           MAlonzo.Code.Once.Adequacy.FunBundle.C_bffi_102 v24 v26 v27 v28 v34
                             -> coe
                                  d_link'45'walk_2450 (coe v0)
                                  (coe
                                     MAlonzo.Code.Once.Compile.C_cscope_636
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v21))
                                           (coe v11))
                                        (coe MAlonzo.Code.Once.Compile.d_csig_630 (coe v1)))
                                     (coe MAlonzo.Code.Once.Compile.d_cimps_632 (coe v1))
                                     (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
                                  (coe v20) (coe v18) (coe v34) (coe v5)
                                  (coe
                                     du_linv'45'sig_1936
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
                                     MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'sig_346
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
      MAlonzo.Code.Once.Lang.Module.C_mono_96 v11 v13 v17 v18 v19
        -> case coe v2 of
             (:) v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v22
                      -> case coe v22 of
                           MAlonzo.Code.Once.Parser.C_mkFunInfo_114 v23 v24 v25 v26
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Adequacy.FunBundle.C_bcons_136 v30 v31 v32 v33 v34 v35 v39 v43
                                    -> coe
                                         seq (coe v31)
                                         (coe
                                            d_link'45'walk_2450 (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.Compile.C_cscope_636
                                               (coe MAlonzo.Code.Once.Compile.d_csig_630 (coe v1))
                                               (coe
                                                  MAlonzo.Code.Once.Compile.d_extendDefs'45'at_680
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                        erased
                                                        (coe
                                                           (\ v44 ->
                                                              coe
                                                                MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_'8801''8658'Pointwise'45''8801'_606
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                   v23)))
                                                        (coe
                                                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                                           (coe
                                                              (\ v44 v45 ->
                                                                 coe
                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                   erased erased
                                                                   (coe
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                      erased
                                                                      (\ v46 ->
                                                                         coe
                                                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                              v44))
                                                                      (coe
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                         (coe
                                                                            eqInt
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                               v44)
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                               v45))
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                                                            (coe
                                                                               eqInt
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                                  v44)
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                                  v45)))))))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                              v23)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe 'm')
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe 'a')
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe 'i')
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                       (coe 'n')
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
                                                  (coe
                                                     MAlonzo.Code.Once.Compile.d_cimps_632 (coe v1))
                                                  (coe v23) (coe v11))
                                               (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
                                            (coe v21) (coe v19) (coe v43)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.Program.C_irFun_24
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Name.C_canonical_12
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
                                                           MAlonzo.Code.Once.Compile.d_directCallIR_72
                                                           (coe v11) (coe v35))))
                                                  (coe
                                                     MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              MAlonzo.Code.Once.Compile.d_directCallIR_72
                                                              (coe v11) (coe v35)))))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           MAlonzo.Code.Once.Compile.d_directCallIR_72
                                                           (coe v11) (coe v35)))))
                                               (coe v5))
                                            (coe
                                               du_linv'45'entry_1964 (coe v5) (coe v23) (coe v11)
                                               (coe v35) (coe v17)
                                               (coe
                                                  du_dc'45'linked_1288 (coe v11)
                                                  (coe
                                                     du_body'45'linkedM_2126 (coe v0) (coe v1)
                                                     (coe v5) (coe v6) (coe v24) (coe v23) (coe v11)
                                                     (coe v25)
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Context.C_'91''93'_48)))
                                               (coe v6))
                                            (coe
                                               MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'fun_328
                                               (coe
                                                  MAlonzo.Code.Once.Parser.C_mkFunInfo_114 (coe v23)
                                                  (coe v24) (coe v25)
                                                  (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
                                               v21 v7)
                                            (coe v8))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Module.C_poly_106 v12 v14 v15
        -> case coe v2 of
             (:) v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v18
                      -> case coe v4 of
                           MAlonzo.Code.Once.Adequacy.FunBundle.C_bpoly_156 v22 v23 v24 v25 v28
                             -> coe
                                  d_link'45'walk_2450 (coe v0)
                                  (coe
                                     MAlonzo.Code.Once.Compile.C_cscope_636
                                     (coe MAlonzo.Code.Once.Compile.d_csig_630 (coe v1))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Module.d_imps_16
                                        (coe
                                           MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_494
                                           (coe v1)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                                           (coe MAlonzo.Code.Once.Compile.d_ctop_640 (coe v1)))
                                        (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1))))
                                  (coe v17) (coe v15) (coe v28) (coe v5)
                                  (coe
                                     du_linv'45'poly_2214
                                     (coe
                                        MAlonzo.Code.Once.Compile.C_cscope_636
                                        (coe MAlonzo.Code.Once.Compile.d_csig_630 (coe v1))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Module.d_imps_16
                                           (coe
                                              MAlonzo.Code.Once.Adequacy.AcceptSound.d_scopeOf_494
                                              (coe v1)))
                                        (coe MAlonzo.Code.Once.Compile.d_ctele_634 (coe v1)))
                                     v18 v12 v14
                                     (coe
                                        MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'head_290
                                        (coe v7))
                                     v6)
                                  (coe
                                     MAlonzo.Code.Once.Adequacy.TelePosition.du_fresh'45'poly_358
                                     (coe v1) (coe v17) (coe v7))
                                  (coe v8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.entry-linked
d_entry'45'linked_2712 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  AgdaAny -> AgdaAny
d_entry'45'linked_2712 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_entry'45'linked_2712 v4 v5
du_entry'45'linked_2712 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  AgdaAny -> AgdaAny
du_entry'45'linked_2712 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_30
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v1)
      MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_52 v9 v10 v11
        -> coe
             seq (coe v9)
             (case coe v10 of
                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'void_30
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v1)
                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'unit_32 -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked.main-linked
d_main'45'linked_2742 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_main'45'linked_2742 v0 v1 v2 v3 v4 v5 ~v6
  = du_main'45'linked_2742 v0 v1 v2 v3 v4 v5
du_main'45'linked_2742 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_main'45'linked_2742 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bffi_102 v8 v10 v11 v12 v18
        -> case coe v2 of
             (:) v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v21
                      -> coe
                           du_main'45'linked_2742 (coe v0)
                           (coe
                              MAlonzo.Code.Once.Compile.d_extendSig_708 (coe v1)
                              (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v21)) (coe v8))
                           (coe v20) (coe v18) (coe v4) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bcons_136 v9 v10 v11 v12 v13 v14 v18 v22
        -> case coe v2 of
             (:) v23 v24
               -> case coe v23 of
                    MAlonzo.Code.Once.Parser.C_e'45'fun_134 v25
                      -> coe
                           du_atMain_2786 (coe v0) (coe v1) (coe v25) (coe v24) (coe v9)
                           (coe v14) (coe v22) (coe v4)
                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v25))
                           (coe
                              MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__76
                              (coe
                                 MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v25)))
                              (coe
                                 MAlonzo.Code.Once.Spec.Name.d_bare_14
                                 (coe ("main" :: Data.Text.Text))))
                           (coe
                              MAlonzo.Code.Once.Type.Sub.d__'60''58''63'__160 (coe v9)
                              (coe MAlonzo.Code.Once.Lang.Module.d_EffUU_168))
                           (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Adequacy.FunBundle.C_bpoly_156 v9 v10 v11 v12 v15
        -> case coe v2 of
             (:) v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Parser.C_e'45'poly_136 v18
                      -> coe
                           du_main'45'linked_2742 (coe v0)
                           (coe MAlonzo.Code.Once.Compile.d_addEntry_716 (coe v1) (coe v18))
                           (coe v17) (coe v15) (coe v4) (coe v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked._.T
d_T_2776 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524]
d_T_2776 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 v17 ~v18 ~v19 ~v20
  = du_T_2776 v3 v17
du_T_2776 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_524]
du_T_2776 v0 v1
  = coe
      MAlonzo.Code.Once.Adequacy.FunBundle.du_bundle'8594'compiled_584
      (coe v0) (coe v1)
-- Once.Adequacy.ProgramLinked._.atMain
d_atMain_2786 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_atMain_2786 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12 ~v13
              ~v14 ~v15 ~v16 v17 v18 ~v19 ~v20 v21 ~v22 v23 v24 v25 ~v26
  = du_atMain_2786 v0 v1 v2 v3 v4 v9 v17 v18 v21 v23 v24 v25
du_atMain_2786 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny
du_atMain_2786 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = case coe v9 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
        -> if coe v12
             then coe
                    seq (coe v13)
                    (case coe v10 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                         -> if coe v14
                              then case coe v15 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                       -> coe
                                            du_entry'45'linked_2712 (coe v16)
                                            (coe
                                               MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45''43''43'_270
                                               (coe
                                                  MAlonzo.Code.Once.Compile.d_tableOf'45'go_1310
                                                  (coe du_T_2776 (coe v3) (coe v6))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Name.C_canonical_12
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe ("main" :: Data.Text.Text))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Once.Compile.d_directCallIR_72
                                                        (coe v4) (coe v5))))
                                               (coe
                                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           MAlonzo.Code.Once.Compile.d_directCallIR_72
                                                           (coe v4) (coe v5)))))
                                               (coe
                                                  MAlonzo.Code.Once.Adequacy.ElaborateLinked.du_linkedAt'45'here_48
                                                  (coe du_e'8242'_2802 (coe v4) (coe v5) (coe v8))))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              else coe
                                     seq (coe v15)
                                     (coe
                                        du_main'45'linked_2742 (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v1)
                                           (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2))
                                           (coe v4))
                                        (coe v3) (coe v6)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe
                                              MAlonzo.Code.Once.Compile.d_irFunOf_1300
                                              (coe
                                                 MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Name.d_bare_14
                                                    (coe
                                                       MAlonzo.Code.Once.Parser.d_funName_106
                                                       (coe v2)))
                                                 (coe v4) (coe v5)))
                                           (coe v7))
                                        (coe v11))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v13)
                    (coe
                       du_main'45'linked_2742 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Compile.d_extendScope_700 (coe v1)
                          (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)) (coe v4))
                       (coe v3) (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Once.Compile.d_irFunOf_1300
                             (coe
                                MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
                                (coe
                                   MAlonzo.Code.Once.Spec.Name.d_bare_14
                                   (coe MAlonzo.Code.Once.Parser.d_funName_106 (coe v2)))
                                (coe v4) (coe v5)))
                          (coe v7))
                       (coe v11))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ProgramLinked._._.n′
d_n'8242'_2800 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8242'_2800 = erased
-- Once.Adequacy.ProgramLinked._._.e′
d_e'8242'_2802 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Compile.T_CScope_622 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__26 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_e'8242'_2802 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
               ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 ~v22 ~v23 ~v24
  = du_e'8242'_2802 v4 v9 v21
du_e'8242'_2802 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_e'8242'_2802 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Compile.d_irFunOf_1300
      (coe
         MAlonzo.Code.Once.Compile.C_mkCompiledFun_538
         (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v2)) (coe v0)
         (coe v1))
-- Once.Adequacy.ProgramLinked.linv₀
d_linv'8320'_2828 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_LInv_1568
d_linv'8320'_2828 ~v0 = du_linv'8320'_2828
du_linv'8320'_2828 :: T_LInv_1568
du_linv'8320'_2828
  = coe
      C_constructor_1636 erased erased
      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      erased
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 v7 v8 ->
            coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
      (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      erased
-- Once.Adequacy.ProgramLinked._.no-poly
d_no'45'poly_2838 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'poly_2838 = erased
-- Once.Adequacy.ProgramLinked.typed-ef
d_typed'45'ef_2858 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_typed'45'ef_2858 ~v0 ~v1 v2 ~v3 ~v4 = du_typed'45'ef_2858 v2
du_typed'45'ef_2858 ::
  AgdaAny -> MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_typed'45'ef_2858 v0 = coe v0
-- Once.Adequacy.ProgramLinked.moduleToProgram-linked
d_moduleToProgram'45'linked_2868 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_moduleToProgram'45'linked_2868 v0 v1 ~v2
  = du_moduleToProgram'45'linked_2868 v0 v1
du_moduleToProgram'45'linked_2868 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_moduleToProgram'45'linked_2868 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.Adequacy.FunBundle.du_node'45'ef_1442
              (coe
                 MAlonzo.Code.Once.Parser.d_guardDistinct_542
                 (coe
                    MAlonzo.Code.Once.Parser.d_thenExtract_634
                    (coe
                       MAlonzo.Code.Once.Parser.d_sigsAdjacent_554
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                    (coe
                       MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_220
                       (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                       (coe
                          MAlonzo.Code.Once.Parser.d_sigsFirst_630
                          (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_36 (coe v0)))
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 du_main'45'linked_2742
                                 (coe MAlonzo.Code.Once.Lang.Module.d_moduleSig_152 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.Compile.C_cscope_636
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                 (coe v3) (coe v7)
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1))
                              (coe
                                 d_link'45'walk_2450
                                 (coe MAlonzo.Code.Once.Lang.Module.d_moduleSig_152 (coe v0))
                                 (coe
                                    MAlonzo.Code.Once.Compile.C_cscope_636
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    (coe
                                       MAlonzo.Code.Once.Compile.d_cimps_632
                                       (coe MAlonzo.Code.Once.Compile.d_emptyCScope_638))
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                 (coe v3) (coe du_mt'8320'_2902 (coe v0)) (coe v7)
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 (coe du_linv'8320'_2828)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.TelePosition.du_entries'45'distinct_486
                                       (coe v0) (coe v3))
                                    (coe
                                       MAlonzo.Code.Once.Adequacy.TelePosition.d_none'45'in'45'empty_498
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_map_22
                                          (coe
                                             MAlonzo.Code.Once.Adequacy.TelePosition.d_entryName_94)
                                          (coe v3))))
                                 (coe (\ v9 v10 -> v10)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.ProgramLinked._.bf
d_bf_2900 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bf_2900 = erased
-- Once.Adequacy.ProgramLinked._.mt₀
d_mt'8320'_2902 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
d_mt'8320'_2902 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_mt'8320'_2902 v0
du_mt'8320'_2902 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Lang.Module.T_ModTele_70
du_mt'8320'_2902 v0
  = coe
      MAlonzo.Code.Once.Adequacy.AcceptSound.du_moduleToIR'45'typed_842
      (coe v0)
-- Once.Adequacy.ProgramLinked._.u
d_u_2906 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Adequacy.FunBundle.T_FunBundle_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_u_2906 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_u_2906 v8
du_u_2906 ::
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_u_2906 v0 = coe v0
