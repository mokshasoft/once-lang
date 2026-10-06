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

module MAlonzo.Code.Once.Spec.Elaboration where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Spec.Core.Derived
import qualified MAlonzo.Code.Once.Spec.Core.DerivedTyping
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Rename
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Spec.Elaboration._.Lit
d_Lit_16 a0 a1 a2 = ()
-- Once.Spec.Elaboration._.Prim
d_Prim_18 a0 a1 a2 = ()
-- Once.Spec.Elaboration._.Tm
d_Tm_24 a0 a1 a2 a3 = ()
-- Once.Spec.Elaboration._.primCod
d_primCod_98 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_primCod_98 ~v0 ~v1 ~v2 = du_primCod_98
du_primCod_98 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_primCod_98
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primCod_58
-- Once.Spec.Elaboration._.primDom
d_primDom_100 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_primDom_100 ~v0 ~v1 ~v2 = du_primDom_100
du_primDom_100 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Type.T_Type_108
du_primDom_100
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56
-- Once.Spec.Elaboration._._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__242 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Spec.Elaboration.InstanceOf
d_InstanceOf_448 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_InstanceOf_448 = erased
-- Once.Spec.Elaboration.Declared
d_Declared_460 a0 a1 a2 a3 a4 = ()
data T_Declared_460
  = C_declared_478 AgdaAny
                   MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
                   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
-- Once.Spec.Elaboration.Declared.honest
d_honest_472 :: T_Declared_460 -> AgdaAny
d_honest_472 v0
  = case coe v0 of
      C_declared_478 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.Declared.rigid
d_rigid_474 ::
  T_Declared_460 -> MAlonzo.Code.Once.Type.Rigid.T_RigidFree_748
d_rigid_474 v0
  = case coe v0 of
      C_declared_478 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.Declared.member
d_member_476 ::
  T_Declared_460 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_member_476 v0
  = case coe v0 of
      C_declared_478 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.ImportAt
d_ImportAt_484 a0 a1 a2 a3 a4 = ()
data T_ImportAt_484
  = C_def_498 MAlonzo.Code.Data.Fin.Base.T_Fin_10
              MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Spec.Elaboration.ImportAt.entryOf
d_entryOf_494 ::
  T_ImportAt_484 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entryOf_494 v0
  = case coe v0 of
      C_def_498 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.ImportAt.instOf
d_instOf_496 ::
  T_ImportAt_484 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instOf_496 v0
  = case coe v0 of
      C_def_498 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.View
d_View_506 a0 a1 a2 a3 a4 a5 = ()
data T_View_506
  = C_constructor_614 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Type.T_Type_108 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ImportAt_484)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Type.T_Type_108 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Declared_460)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Type.T_PolyType_254 ->
                       MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Fin.Base.T_Fin_10)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Type.T_PolyType_254 ->
                       MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Type.T_PolyType_254 ->
                       MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                       MAlonzo.Code.Once.Type.T_Type_108 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Spec.Elaboration.View.imported
d_imported_568 ::
  T_View_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ImportAt_484
d_imported_568 v0
  = case coe v0 of
      C_constructor_614 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.View.declares
d_declares_574 ::
  T_View_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Declared_460
d_declares_574 v0
  = case coe v0 of
      C_constructor_614 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.View.entry
d_entry_584 ::
  T_View_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_584 v0
  = case coe v0 of
      C_constructor_614 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.View.ground
d_ground_598 ::
  T_View_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground_598 v0
  = case coe v0 of
      C_constructor_614 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.View.inst
d_inst_612 ::
  T_View_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst_612 v0
  = case coe v0 of
      C_constructor_614 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.Views
d_Views_616 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 -> ()
d_Views_616 = erased
-- Once.Spec.Elaboration.Elab
d_Elab_622 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_Elab_622 = erased
-- Once.Spec.Elaboration.lift1
d_lift1_654 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lift1_654 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_lift1_654 v9 v10 v11
du_lift1_654 ::
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lift1_654 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v3)
             (coe v1 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.lift2
d_lift2_674 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lift2_674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            v13 v14
  = du_lift2_674 v11 v12 v13 v14
du_lift2_674 ::
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lift2_674 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v4 v6)
                    (coe v1 v4 v6 v5 v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.appC
d_appC_690 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_appC_690 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 v9
  = du_appC_690 v3 v5 v7 v8 v9
du_appC_690 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_appC_690 v0 v1 v2 v3 v4
  = coe
      du_lift1_654
      (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70 (coe v3))
      (coe
         (\ v5 ->
            coe
              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
              (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)) v2
              (coe MAlonzo.Code.Once.Type.C_Many_10) v1 v4))
-- Once.Spec.Elaboration.bin
d_bin_698 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bin_698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10
  = du_bin_698 v7 v8 v9
du_bin_698 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin_698 v0 v1 v2
  = coe
      du_lift2_674
      (coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Once.Spec.Core.Syntax.C_prim_102 (coe v2)
              (coe
                 MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76 (coe v3) (coe v4))))
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'prim_564
              (coe
                 MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342 v0 v1 v5 v6)))
-- Once.Spec.Elaboration.i2f
d_i2f_714 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_i2f_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_i2f_714
du_i2f_714 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_i2f_714
  = coe
      du_lift1_654
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_prim_102
         (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'i2f_54))
      (coe
         (\ v0 -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'prim_564))
-- Once.Spec.Elaboration.coerceE
d_coerceE_716 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coerceE_716 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 v8
  = du_coerceE_716 v3 v4 v8
du_coerceE_716 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_coerceE_716 v0 v1 v2
  = coe
      du_lift1_654
      (coe
         MAlonzo.Code.Once.Spec.Core.Syntax.C_coerce_98 (coe v0) (coe v1))
      (coe
         (\ v3 ->
            coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'coerce_534 v2))
-- Once.Spec.Elaboration.refE
d_refE_726 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refE_726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_refE_726 v6 v7
du_refE_726 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refE_726 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Syntax.C_ref_108 (coe v0) (coe v2))
                    (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'ref_586 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.sigE
d_sigE_742 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  T_Declared_460 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigE_742 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8
  = du_sigE_742 v3 v6 v7 v8
du_sigE_742 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  T_Declared_460 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigE_742 v0 v1 v2 v3
  = case coe v3 of
      C_declared_478 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Spec.Core.Syntax.C_sigop_104 (coe v1) (coe v0))
             (coe
                MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sigop_576 v2 v4 v5 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.importE
d_importE_758 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_ImportAt_484 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_importE_758 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_importE_758 v7
du_importE_758 ::
  T_ImportAt_484 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_importE_758 v0
  = case coe v0 of
      C_def_498 v1 v2 -> coe du_refE_726 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.closeE
d_closeE_764 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closeE_764 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_closeE_764 v3 v5 v6
du_closeE_764 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_closeE_764 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Core.Rename.du_close_914 v3)
             (coe
                MAlonzo.Code.Once.Spec.Core.Rename.du_'8866'close_926 (coe v1)
                (coe v3) (coe v0) (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.subE
d_subE_770 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subE_770 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_subE_770 v9
du_subE_770 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_subE_770 v0 = coe v0
-- Once.Spec.Elaboration.elabᶜ
d_elab'7580'_782 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_View_506 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7580'_782 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_428
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v12 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Once.Spec.Core.Derived.du_id'7580'_260)
                           (coe
                              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                              (coe MAlonzo.Code.Once.Type.C_One_8)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                                 (coe MAlonzo.Code.Once.Type.C_pure_34)
                                 (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v16))
                                 (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_438
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
               -> case coe v13 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v16 v17
                      -> case coe v14 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe MAlonzo.Code.Once.Spec.Core.Derived.du_fst'7580'_264)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                                     (coe MAlonzo.Code.Once.Type.C_One_8)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v17
                                        (coe
                                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                                           (coe MAlonzo.Code.Once.Type.C_pure_34)
                                           (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v19))
                                           (coe
                                              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_448
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
               -> case coe v13 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v16 v17
                      -> case coe v14 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe MAlonzo.Code.Once.Spec.Core.Derived.du_snd'7580'_268)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                                     (coe MAlonzo.Code.Once.Type.C_One_8)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374 v16
                                        (coe
                                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                                           (coe MAlonzo.Code.Once.Type.C_pure_34)
                                           (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v19))
                                           (coe
                                              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_456
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v12 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Once.Spec.Core.Derived.du_terminal'7580'_280)
                           (coe
                              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                                 (coe MAlonzo.Code.Once.Type.C_pure_34)
                                 (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v16))
                                 (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_464
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v12 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Once.Spec.Core.Derived.du_initial'7580'_284)
                           (coe
                              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                              (coe MAlonzo.Code.Once.Type.C_One_8)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_448
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                                    (coe MAlonzo.Code.Once.Type.C_pure_34)
                                    (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v16))
                                    (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_474
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Once.Spec.Core.Derived.du_inl'7580'_272)
                           (coe
                              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                              (coe MAlonzo.Code.Once.Type.C_One_8)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                                    (coe MAlonzo.Code.Once.Type.C_pure_34)
                                    (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v17))
                                    (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_484
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Once.Spec.Core.Derived.du_inr'7580'_276)
                           (coe
                              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                              (coe MAlonzo.Code.Once.Type.C_One_8)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                                    (coe MAlonzo.Code.Once.Type.C_pure_34)
                                    (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v17))
                                    (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_504 v13 v16 v17 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
                      -> case coe v5 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v24 v25 v26
                             -> case coe v25 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v27 v28
                                    -> coe
                                         du_lift2_674
                                         (coe
                                            MAlonzo.Code.Once.Spec.Core.Derived.du_compose'7580'_300)
                                         (\ v29 v30 v31 v32 ->
                                            coe
                                              MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'compose'7580'_584
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_394
                                                 (coe v3))
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                                                 (coe v3))
                                              (coe v16) (coe v17) (coe v24) (coe v13) (coe v26)
                                              (coe v28) v30 v31 v32)
                                         (coe
                                            d_elab'7580'_782 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v23)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v28))
                                               (coe v26))
                                            (coe v16) (coe v7) (coe v19))
                                         (coe
                                            d_elab'7496'_806 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v21) (coe v24) (coe v13) (coe v28) (coe v17)
                                            (coe v7) (coe v18))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_528 v13 v15 v17 v18 v19 v20 v21 v22
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
               -> case coe v23 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v25 v26
                      -> case coe v5 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v27 v28 v29
                             -> case coe v28 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v30 v31
                                    -> coe
                                         du_lift2_674
                                         (coe
                                            MAlonzo.Code.Once.Spec.Core.Derived.du_compose'7580'_300)
                                         (\ v32 v33 v34 v35 ->
                                            coe
                                              MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'compose'7580'_584
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_394
                                                 (coe v3))
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                                                 (coe v3))
                                              (coe v18) (coe v19) (coe v27) (coe v13) (coe v29)
                                              (coe v31) v33 v34 v35)
                                         (coe
                                            du_coerceE_716
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v17))
                                               (coe v15))
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v31))
                                               (coe v29))
                                            v21
                                            (d_elab'7522'_792
                                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v26)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe v17))
                                                  (coe v15))
                                               (coe v18) (coe v7) (coe v20)))
                                         (coe
                                            d_elab'7580'_782 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v24)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v27)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v31))
                                               (coe v13))
                                            (coe v19) (coe v7) (coe v22))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_548 v16 v17 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
                      -> case coe v5 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v24 v25 v26
                             -> case coe v24 of
                                  MAlonzo.Code.Once.Type.C__'43'__126 v27 v28
                                    -> case coe v25 of
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 v29 v30
                                           -> coe
                                                du_lift2_674
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Core.Derived.du_case'7580'_316)
                                                (\ v31 v32 v33 v34 ->
                                                   coe
                                                     MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'case'7580'_668
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_394
                                                        (coe v3))
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                                                        (coe v3))
                                                     (coe v16) (coe v17) (coe v27) (coe v28)
                                                     (coe v26) (coe v30) v32 v33 v34)
                                                (coe
                                                   d_elab'7580'_782 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v23)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v27)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v30))
                                                      (coe v26))
                                                   (coe v16) (coe v7) (coe v18))
                                                (coe
                                                   d_elab'7580'_782 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v21)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v28)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v30))
                                                      (coe v26))
                                                   (coe v17) (coe v7) (coe v19))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_568 v16 v17 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
                      -> case coe v5 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v24 v25 v26
                             -> case coe v25 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v27 v28
                                    -> case coe v26 of
                                         MAlonzo.Code.Once.Type.C__'42'__124 v29 v30
                                           -> coe
                                                du_lift2_674
                                                (coe
                                                   MAlonzo.Code.Once.Spec.Core.Derived.du_pair'7580'_308)
                                                (\ v31 v32 v33 v34 ->
                                                   coe
                                                     MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'pair'7580'_630
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_394
                                                        (coe v3))
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                                                        (coe v3))
                                                     (coe v16) (coe v17) (coe v24) (coe v29)
                                                     (coe v30) (coe v28) v32 v33 v34)
                                                (coe
                                                   d_elab'7580'_782 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v23)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v24)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v28))
                                                      (coe v29))
                                                   (coe v16) (coe v7) (coe v18))
                                                (coe
                                                   d_elab'7580'_782 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v21)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe v24)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v28))
                                                      (coe v30))
                                                   (coe v17) (coe v7) (coe v19))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_586 v17
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                             -> case coe v22 of
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v25 v26 v27
                                    -> case coe v26 of
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 v28 v29
                                           -> coe
                                                du_lift1_654
                                                (coe
                                                   (\ v30 ->
                                                      coe
                                                        MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72
                                                        (coe v30)
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
                                                              (coe
                                                                 MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70
                                                                 (coe
                                                                    MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                                                                    (coe
                                                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                       (coe
                                                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                          (coe
                                                                             MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76
                                                                    (coe
                                                                       MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                                                                       (coe
                                                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                          (coe
                                                                             MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66
                                                                       (coe
                                                                          MAlonzo.Code.Data.Fin.Base.C_zero_12))))))))
                                                (\ v30 v31 ->
                                                   coe
                                                     MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'curry'7580'_706
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_394
                                                        (coe v3))
                                                     (coe v6) (coe v20) (coe v25) (coe v27)
                                                     (coe v24) (coe v29) v31)
                                                (coe
                                                   d_elab'7580'_782 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C__'42'__124
                                                         (coe v20) (coe v25))
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v29))
                                                      (coe v27))
                                                   (coe v6) (coe v7) (coe v17))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_600 v15 v16
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
                      -> case coe v19 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_130 v22
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                                    -> coe
                                         du_lift1_654
                                         (coe MAlonzo.Code.Once.Spec.Core.Derived.du_cata'7580'_330)
                                         (coe
                                            (\ v25 ->
                                               coe
                                                 MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'cata'7580'_738
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_size_394
                                                    (coe v3))
                                                 (coe v6) (coe v22) (coe v21) (coe v24) (coe v15)))
                                         (coe
                                            d_elab'7580'_782 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v18)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe
                                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                  (coe v22) (coe v21))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v24))
                                               (coe v21))
                                            (coe v6) (coe v7) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'ana'45'check_616 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v20 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                             -> case coe v22 of
                                  MAlonzo.Code.Once.Type.C_ν'45'type_132 v25 v26
                                    -> coe
                                         du_lift1_654
                                         (coe MAlonzo.Code.Once.Spec.Core.Derived.du_ana'7580'_334)
                                         (coe
                                            (\ v27 ->
                                               coe
                                                 MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'ana'7580'_768
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_size_394
                                                    (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                                                    (coe v3))
                                                 (coe v6) (coe v25) (coe v20) (coe v24) (coe v26)
                                                 (coe v27) (coe v16)))
                                         (coe
                                            d_elab'7580'_782 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v19)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                               (coe v20)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v26))
                                               (coe
                                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                  (coe v25) (coe v20)))
                                            (coe v6) (coe v7) (coe v17))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_628 v11 v14 v15
        -> coe
             du_coerceE_716 v11 v5 v15
             (d_elab'7522'_792
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v11) (coe v6)
                (coe v7) (coe v14))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_648 v15 v19
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v20 v21
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v22 v23 v24
                      -> case coe v23 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           d_elab'7580'_782 (coe v0) (coe v1) (coe v2)
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                                              (coe
                                                 addInt (coe (1 :: Integer))
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_size_394
                                                    (coe v3)))
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_named_396
                                                    (coe v3))
                                                 (coe v20) (coe v22))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                                                    (coe v3))
                                                 (coe v22))
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_400
                                                 (coe v3))
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402
                                                 (coe v3))
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_polys_404
                                                 (coe v3))
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406
                                                 (coe v3)))
                                           (coe v21) (coe v24)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15
                                              v6)
                                           (coe v7) (coe v19))))
                                  (coe
                                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272 v15
                                     (coe
                                        MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                                        (coe MAlonzo.Code.Once.Type.C_pure_34)
                                        (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v26))
                                        (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              d_elab'7580'_782 (coe v0) (coe v1) (coe v2)
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                                                 (coe
                                                    addInt (coe (1 :: Integer))
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_size_394
                                                       (coe v3)))
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_named_396
                                                       (coe v3))
                                                    (coe v20) (coe v22))
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                                                       (coe v3))
                                                    (coe v22))
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_400
                                                    (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402
                                                    (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_polys_404
                                                    (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406
                                                    (coe v3)))
                                              (coe v21) (coe v24)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15
                                                 v6)
                                              (coe v7) (coe v19)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_664 v14 v15 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v18 v19
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v20 v21
                      -> coe
                           du_lift2_674 (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76)
                           (\ v22 v23 v24 v25 ->
                              coe
                                MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342 v14 v15 v24
                                v25)
                           (coe
                              d_elab'7580'_782 (coe v0) (coe v1) (coe v2) (coe v3) (coe v18)
                              (coe v20) (coe v14) (coe v7) (coe v16))
                           (coe
                              d_elab'7580'_782 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe v21) (coe v15) (coe v7) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_674 v12 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v17
                      -> coe
                           du_appC_690
                           (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                           (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v17) (coe v5))
                           v12 (coe MAlonzo.Code.Once.Spec.Core.Derived.du_in'7580'_292)
                           (coe
                              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                              (coe MAlonzo.Code.Once.Type.C_One_8)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_462 v13
                                 (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
                           (d_elab'7580'_782
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v17) (coe v5))
                              (coe v12) (coe v7) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_686 v11 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    du_appC_690
                    (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                    (coe
                       MAlonzo.Code.Once.Type.C__'42'__124
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v5))
                       (coe v11))
                    v13 (coe MAlonzo.Code.Once.Spec.Core.Derived.du_apply'7580'_288)
                    (coe
                       MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'apply'7580'_792
                       (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                       (coe v11) (coe v5))
                    (d_elab'7522'_792
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__124
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v11)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v5))
                          (coe v11))
                       (coe v13) (coe v7) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_698 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v17 v18
                      -> coe
                           du_appC_690
                           (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)) v17 v13
                           (coe MAlonzo.Code.Once.Spec.Core.Derived.du_inl'7580'_272)
                           (coe
                              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                              (coe MAlonzo.Code.Once.Type.C_One_8)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                                    (coe MAlonzo.Code.Once.Type.C_pure_34)
                                    (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16
                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                    (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
                           (d_elab'7580'_782
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v16) (coe v17) (coe v13)
                              (coe v7) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_710 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v17 v18
                      -> coe
                           du_appC_690
                           (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)) v18 v13
                           (coe MAlonzo.Code.Once.Spec.Core.Derived.du_inr'7580'_276)
                           (coe
                              MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                              (coe MAlonzo.Code.Once.Type.C_One_8)
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                                    (coe MAlonzo.Code.Once.Type.C_pure_34)
                                    (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16
                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                    (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
                           (d_elab'7580'_782
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v16) (coe v18) (coe v13)
                              (coe v7) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_720 v12 v13
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    du_appC_690
                    (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                    (coe MAlonzo.Code.Once.Type.C_Void_122) v12
                    (coe MAlonzo.Code.Once.Spec.Core.Derived.du_initial'7580'_284)
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                       (coe MAlonzo.Code.Once.Type.C_One_8)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_448
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                             (coe MAlonzo.Code.Once.Type.C_pure_34)
                             (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
                    (d_elab'7580'_782
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                       (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v12) (coe v7)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_734 v12 v13 v14 v19
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v20
               -> coe
                    du_refE_726 (coe d_entry_584 v7 v20 v12 v13 v14 erased)
                    (coe d_inst_612 v7 v20 v12 v13 v14 v5 erased erased v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.elabᵢ
d_elab'7522'_792 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_View_506 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7522'_792 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Syntax.C_lit_100
                       (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_lit'45'int_16 (coe v11)))
                    (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'int_542)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v14 v15 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Syntax.C_lit_100
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Syntax.C_lit'45'float_18
                          (coe
                             MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v14) (coe v15)
                             (coe v16))))
                    (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'float_550)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_46
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_unit_74)
             (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_50
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_unit_74)
             (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_62 v13
        -> case coe v13 of
             MAlonzo.Code.Once.Surface.Context.C_svar_218 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_var_66 (coe v17))
                    (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_72 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v15 v16
               -> coe
                    du_sigE_742 (coe v5)
                    (coe
                       MAlonzo.Code.Once.CanonicalName.d_bare_12
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v16
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("." :: Data.Text.Text) v15)))
                    (coe v14)
                    (coe
                       d_declares_574 v7
                       (MAlonzo.Code.Once.CanonicalName.d_showCanonical_140
                          (coe
                             MAlonzo.Code.Once.CanonicalName.d_bare_12
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v16
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   ("." :: Data.Text.Text) v15))))
                       v5 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_80 v12 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v15
               -> coe
                    du_sigE_742 (coe v5) (coe v15) (coe v14)
                    (coe
                       d_declares_574 v7
                       (MAlonzo.Code.Once.CanonicalName.d_showCanonical_140 (coe v15)) v5
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'own_88 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v15
               -> case coe v15 of
                    MAlonzo.Code.Once.CanonicalName.C_canonical_10 v16
                      -> case coe v16 of
                           (:) v17 v18
                             -> coe du_importE_758 (coe d_imported_568 v7 v17 v5 erased)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_96 v15
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v16
               -> coe du_importE_758 (coe d_imported_568 v7 v16 v5 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_112 v12 v13 v14 v15 v19
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v21
               -> coe
                    du_refE_726 (coe d_entry_584 v7 v21 v12 v13 v14 erased)
                    (coe d_ground_598 v7 v21 v12 v13 v14 erased v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_122 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v15 v16
               -> coe
                    d_elab'7580'_782 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                    (coe v5) (coe v6) (coe v7) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_138 v14 v15 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v18 v19
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v20 v21
                      -> coe
                           du_lift2_674 (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76)
                           (\ v22 v23 v24 v25 ->
                              coe
                                MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342 v14 v15 v24
                                v25)
                           (coe
                              d_elab'7522'_792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v18)
                              (coe v20) (coe v14) (coe v7) (coe v16))
                           (coe
                              d_elab'7522'_792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe v21) (coe v15) (coe v7) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_146 v12
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v14
               -> coe
                    du_lift1_654
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Syntax.C_prim_102
                       (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'neg_32))
                    (coe
                       (\ v15 -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'prim_564))
                    (coe
                       d_elab'7522'_792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
                       (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v6) (coe v7) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_158
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v15
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v16 v17 v18 v19
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Spec.Core.Syntax.C_lit_100
                              (coe
                                 MAlonzo.Code.Once.Spec.Core.Syntax.C_lit'45'float_18
                                 (coe
                                    MAlonzo.Code.Once.Float.Decimal.d_negate_22
                                    (coe
                                       MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v16)
                                       (coe v17) (coe v18)))))
                           (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'float_550)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_178 v13 v15 v16 v17 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v20 v21 v22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                             (coe v13) (coe v16) (coe v7) (coe v18)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_792 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_396 (coe v3))
                                   (coe v20) (coe v13))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v3))
                                   (coe v13))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_400 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_404 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406 (coe v3)))
                             (coe v22) (coe v5)
                             (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v17)
                             (coe v7) (coe v19))))
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v16 v17 v15 v13
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_elab'7522'_792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                             (coe v13) (coe v16) (coe v7) (coe v18)))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_elab'7522'_792 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_396 (coe v3))
                                   (coe v20) (coe v13))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v3))
                                   (coe v13))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_400 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_404 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406 (coe v3)))
                             (coe v22) (coe v5)
                             (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v17)
                             (coe v7) (coe v19))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_208 v15 v16 v18 v19 v20 v21 v22 v23 v24 v25
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v26 v27 v28 v29 v30
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Syntax.C_case_86
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v26)
                             (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v15) (coe v16))
                             (coe v20) (coe v7) (coe v23)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_792 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_396 (coe v3))
                                   (coe v27) (coe v15))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v3))
                                   (coe v15))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_400 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_404 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406 (coe v3)))
                             (coe v28) (coe v5)
                             (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v18 v21)
                             (coe v7) (coe v24)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_792 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_396 (coe v3))
                                   (coe v29) (coe v16))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v3))
                                   (coe v16))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_400 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_404 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406 (coe v3)))
                             (coe v30) (coe v5)
                             (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v19 v22)
                             (coe v7) (coe v25))))
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.du_'8866'case'8852'_664
                       (coe v20) (coe v21) (coe v22) (coe v18) (coe v19) (coe v15)
                       (coe v16)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_elab'7522'_792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v26)
                             (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v15) (coe v16))
                             (coe v20) (coe v7) (coe v23)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_elab'7522'_792 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_396 (coe v3))
                                   (coe v27) (coe v15))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v3))
                                   (coe v15))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_400 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_404 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406 (coe v3)))
                             (coe v28) (coe v5)
                             (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v18 v21)
                             (coe v7) (coe v24)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_elab'7522'_792 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_396 (coe v3))
                                   (coe v29) (coe v16))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v3))
                                   (coe v16))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_400 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_404 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406 (coe v3)))
                             (coe v30) (coe v5)
                             (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v19 v22)
                             (coe v7) (coe v25))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_222 v13 v14 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'add_22)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'sub_24)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'mul_26)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'div_28)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'mod_30)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_236 v13 v14 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fadd_46)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fsub_48)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fmul_50)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fdiv_52)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v14) (coe v7)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_250 v13 v14 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fadd_46)
                           (coe
                              du_i2f_714
                              (d_elab'7522'_792
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                                 (coe v16)))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fsub_48)
                           (coe
                              du_i2f_714
                              (d_elab'7522'_792
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                                 (coe v16)))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fmul_50)
                           (coe
                              du_i2f_714
                              (d_elab'7522'_792
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                                 (coe v16)))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fdiv_52)
                           (coe
                              du_i2f_714
                              (d_elab'7522'_792
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                                 (coe v16)))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v14) (coe v7)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_264 v13 v14 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fadd_46)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v13) (coe v7)
                              (coe v16))
                           (coe
                              du_i2f_714
                              (d_elab'7522'_792
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                                 (coe v17)))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fsub_48)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v13) (coe v7)
                              (coe v16))
                           (coe
                              du_i2f_714
                              (d_elab'7522'_792
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                                 (coe v17)))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fmul_50)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v13) (coe v7)
                              (coe v16))
                           (coe
                              du_i2f_714
                              (d_elab'7522'_792
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                                 (coe v17)))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'fdiv_52)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v13) (coe v7)
                              (coe v16))
                           (coe
                              du_i2f_714
                              (d_elab'7522'_792
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                                 (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                                 (coe v17)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_278 v13 v14 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'lt_34)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'le_36)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'gt_38)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'ge_40)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'eq_42)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                      -> coe
                           du_bin_698 v13 v14
                           (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_p'45'ne_44)
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v14) (coe v7)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_288 v12 v13
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    du_appC_690
                    (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)) v5 v12
                    (coe MAlonzo.Code.Once.Spec.Core.Derived.du_id'7580'_260)
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                       (coe MAlonzo.Code.Once.Type.C_One_8)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                          (coe MAlonzo.Code.Once.Type.C_pure_34)
                          (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
                    (d_elab'7522'_792
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v15) (coe v5) (coe v12)
                       (coe v7) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_300 v12 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    du_appC_690
                    (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                    (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v5) (coe v12)) v13
                    (coe MAlonzo.Code.Once.Spec.Core.Derived.du_fst'7580'_264)
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                       (coe MAlonzo.Code.Once.Type.C_One_8)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v12
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                             (coe MAlonzo.Code.Once.Type.C_pure_34)
                             (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
                    (d_elab'7522'_792
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v5) (coe v12))
                       (coe v13) (coe v7) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_312 v11 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    du_appC_690
                    (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                    (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v11) (coe v5)) v13
                    (coe MAlonzo.Code.Once.Spec.Core.Derived.du_snd'7580'_268)
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                       (coe MAlonzo.Code.Once.Type.C_One_8)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374 v11
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                             (coe MAlonzo.Code.Once.Type.C_pure_34)
                             (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
                    (d_elab'7522'_792
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v11) (coe v5))
                       (coe v13) (coe v7) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_322 v11 v12 v13
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    du_appC_690
                    (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)) v11 v12
                    (coe MAlonzo.Code.Once.Spec.Core.Derived.du_terminal'7580'_280)
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                       (coe MAlonzo.Code.Once.Type.C_Zero_6)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                          (coe MAlonzo.Code.Once.Type.C_pure_34)
                          (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322)))
                    (d_elab'7522'_792
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v15) (coe v11) (coe v12)
                       (coe v7) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_334 v11 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    du_appC_690
                    (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                    (coe
                       MAlonzo.Code.Once.Type.C__'42'__124
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v5))
                       (coe v11))
                    v13 (coe MAlonzo.Code.Once.Spec.Core.Derived.du_apply'7580'_288)
                    (coe
                       MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'apply'7580'_792
                       (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                       (coe v11) (coe v5))
                    (d_elab'7522'_792
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__124
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v11)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v5))
                          (coe v11))
                       (coe v13) (coe v7) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_346 v11 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
                      -> coe
                           du_appC_690
                           (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                           (coe
                              MAlonzo.Code.Once.Type.C__'42'__124
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v19))
                              (coe v11))
                           v13 (coe MAlonzo.Code.Once.Spec.Core.Derived.du_applyEff'7580'_358)
                           (coe
                              MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'applyEff'7580'_826
                              (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                              (coe v11) (coe v19))
                           (d_elab'7522'_792
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'42'__124
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v11)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                    (coe v19))
                                 (coe v11))
                              (coe v13) (coe v7) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_358 v11 v13 v14 v16
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    du_appC_690
                    (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                    (coe
                       MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v11)
                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                    v13 (coe MAlonzo.Code.Once.Spec.Core.Derived.du_out'7580'_296)
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                       (coe MAlonzo.Code.Once.Type.C_One_8)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_518 v11 v14
                          (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
                    (d_elab'7522'_792
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v18)
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v11)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v13) (coe v7) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_370 v11 v13 v14 v16
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    du_appC_690
                    (MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                    (coe
                       MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v11)
                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                    v13 (coe MAlonzo.Code.Once.Spec.Core.Derived.du_outEff'7580'_362)
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                       (coe MAlonzo.Code.Once.Type.C_One_8)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                          (coe MAlonzo.Code.Once.Type.C_Zero_6)
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_518 v11 v14
                             (coe
                                MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                                (coe MAlonzo.Code.Once.Type.C_pure_34)
                                (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16
                                   (coe MAlonzo.Code.Once.Type.C_eff_36))
                                (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))))
                    (d_elab'7522'_792
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v18)
                       (coe
                          MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v11)
                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                       (coe v13) (coe v7) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_388 v12 v14 v15 v16 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
               -> coe
                    du_lift2_674 (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70)
                    (\ v22 v23 v24 v25 ->
                       coe
                         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294 v15 v16 v14 v12
                         v24 v25)
                    (coe
                       d_elab'7522'_792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v12)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v14)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v5))
                       (coe v15) (coe v7) (coe v18))
                    (coe
                       d_elab'7580'_782 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                       (coe v12) (coe v16) (coe v7) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_404 v12 v14 v15 v17 v18
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v21 v22 v23
                      -> coe
                           du_lift2_674
                           (coe MAlonzo.Code.Once.Spec.Core.Derived.du_effApp'7580'_342)
                           (coe
                              MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'effApp'7580'_858
                              (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v3))
                              (coe v14) (coe v15) (coe v12) (coe v23))
                           (coe
                              d_elab'7522'_792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v12)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v23))
                              (coe v14) (coe v7) (coe v17))
                           (coe
                              d_elab'7580'_782 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe v12) (coe v15) (coe v7) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_420 v12 v14 v15 v17 v18
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> coe
                    du_lift2_674 (coe MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70)
                    (\ v21 v22 v23 v24 ->
                       coe
                         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294 v14 v15
                         (coe MAlonzo.Code.Once.Type.C_Many_10) v12 v23 v24)
                    (coe
                       d_elab'7496'_806 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                       (coe v12) (coe v5) (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v14)
                       (coe v7) (coe v18))
                    (coe
                       d_elab'7522'_792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                       (coe v12) (coe v15) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Elaboration.elabᵈ
d_elab'7496'_806 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  T_View_506 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7496'_806 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_752 v14 v17 v19 v20 v21
        -> coe
             du_coerceE_716
             (coe
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v14)
                (coe
                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v17))
                (coe v6))
             (coe
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v5)
                (coe
                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
                (coe v6))
             (coe
                MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74 v20
                (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v6)) v21)
             (d_elab'7522'_792
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v14)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                      (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v17))
                   (coe v6))
                (coe v8) (coe v9) (coe v19))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_776 v16 v17 v18 v19 v20 v21 v26 v27 v28 v29
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v30
               -> coe
                    du_coerceE_716
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v16))
                       (coe v6))
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
                       (coe v6))
                    (coe
                       MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74
                       (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v5))
                       (MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v6)) v29)
                    (coe
                       du_refE_726 (coe d_entry_584 v9 v30 v17 v20 v21 erased)
                       (coe
                          d_inst_612 v9 v30 v17 v20 v21
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v16))
                             (coe v6))
                          erased erased v28))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_794 v16 v20
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v21 v22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_792 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_396 (coe v3))
                                   (coe v21) (coe v5))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v3))
                                   (coe v5))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_400 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_404 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406 (coe v3)))
                             (coe v22) (coe v6)
                             (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v16 v8)
                             (coe v9) (coe v20))))
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272 v16
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                          (coe MAlonzo.Code.Once.Type.C_pure_34)
                          (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_elab'7522'_792 (coe v0) (coe v1) (coe v2)
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_408
                                   (coe
                                      addInt (coe (1 :: Integer))
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3)))
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_named_396 (coe v3))
                                      (coe v21) (coe v5))
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                                         (coe v3))
                                      (coe v5))
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_400
                                      (coe v3))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_402 (coe v3))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_404 (coe v3))
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_sig_406 (coe v3)))
                                (coe v22) (coe v6)
                                (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v16 v8)
                                (coe v9) (coe v20)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_814 v15 v18 v19 v20 v21
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v24 v25
                      -> coe
                           du_lift2_674
                           (coe MAlonzo.Code.Once.Spec.Core.Derived.du_compose'7580'_300)
                           (\ v26 v27 v28 v29 ->
                              coe
                                MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'compose'7580'_584
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398 (coe v3))
                                (coe v18) (coe v19) (coe v5) (coe v15) (coe v6) (coe v7) v27 v28
                                v29)
                           (coe
                              d_elab'7496'_806 (coe v0) (coe v1) (coe v2) (coe v3) (coe v25)
                              (coe v15) (coe v6) (coe v7) (coe v18) (coe v9) (coe v21))
                           (coe
                              d_elab'7496'_806 (coe v0) (coe v1) (coe v2) (coe v3) (coe v23)
                              (coe v5) (coe v15) (coe v7) (coe v19) (coe v9) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_822
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Core.Derived.du_id'7580'_260)
             (coe
                MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                (coe MAlonzo.Code.Once.Type.C_One_8)
                (coe
                   MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                   (coe MAlonzo.Code.Once.Type.C_pure_34)
                   (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                   (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_832
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'42'__124 v15 v16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Spec.Core.Derived.du_fst'7580'_264)
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                       (coe MAlonzo.Code.Once.Type.C_One_8)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v16
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                             (coe MAlonzo.Code.Once.Type.C_pure_34)
                             (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                             (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_842
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C__'42'__124 v15 v16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Spec.Core.Derived.du_snd'7580'_268)
                    (coe
                       MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                       (coe MAlonzo.Code.Once.Type.C_One_8)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374 v15
                          (coe
                             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                             (coe MAlonzo.Code.Once.Type.C_pure_34)
                             (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                             (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_850
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Core.Derived.du_terminal'7580'_280)
             (coe
                MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                (coe MAlonzo.Code.Once.Type.C_Zero_6)
                (coe
                   MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                   (coe MAlonzo.Code.Once.Type.C_pure_34)
                   (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                   (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_856
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Spec.Core.Derived.du_initial'7580'_284)
             (coe
                MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
                (coe MAlonzo.Code.Once.Type.C_One_8)
                (coe
                   MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_448
                   (coe
                      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                      (coe MAlonzo.Code.Once.Type.C_pure_34)
                      (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                      (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_876 v18 v19 v20 v21
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v24 v25
                      -> case coe v5 of
                           MAlonzo.Code.Once.Type.C__'43'__126 v26 v27
                             -> coe
                                  du_lift2_674
                                  (coe MAlonzo.Code.Once.Spec.Core.Derived.du_case'7580'_316)
                                  (\ v28 v29 v30 v31 ->
                                     coe
                                       MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'case'7580'_668
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                                          (coe v3))
                                       (coe v18) (coe v19) (coe v26) (coe v27) (coe v6) (coe v7) v29
                                       v30 v31)
                                  (coe
                                     d_elab'7496'_806 (coe v0) (coe v1) (coe v2) (coe v3) (coe v25)
                                     (coe v26) (coe v6) (coe v7) (coe v18) (coe v9) (coe v20))
                                  (coe
                                     d_elab'7496'_806 (coe v0) (coe v1) (coe v2) (coe v3) (coe v23)
                                     (coe v27) (coe v6) (coe v7) (coe v19) (coe v9) (coe v21))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_896 v18 v19 v20 v21
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v24 v25
                      -> case coe v6 of
                           MAlonzo.Code.Once.Type.C__'42'__124 v26 v27
                             -> coe
                                  du_lift2_674
                                  (coe MAlonzo.Code.Once.Spec.Core.Derived.du_pair'7580'_308)
                                  (\ v28 v29 v30 v31 ->
                                     coe
                                       MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'pair'7580'_630
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_398
                                          (coe v3))
                                       (coe v18) (coe v19) (coe v5) (coe v26) (coe v27) (coe v7) v29
                                       v30 v31)
                                  (coe
                                     d_elab'7496'_806 (coe v0) (coe v1) (coe v2) (coe v3) (coe v25)
                                     (coe v5) (coe v26) (coe v7) (coe v18) (coe v9) (coe v20))
                                  (coe
                                     d_elab'7496'_806 (coe v0) (coe v1) (coe v2) (coe v3) (coe v23)
                                     (coe v5) (coe v27) (coe v7) (coe v19) (coe v9) (coe v21))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_910 v17 v18
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v21
                      -> coe
                           du_lift1_654
                           (coe MAlonzo.Code.Once.Spec.Core.Derived.du_cata'7580'_330)
                           (coe
                              (\ v22 ->
                                 coe
                                   MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'cata'7580'_738
                                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_394 (coe v3))
                                   (coe v8) (coe v21) (coe v6) (coe v7) (coe v17)))
                           (coe
                              d_elab'7522'_792 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                 (coe
                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v21)
                                    (coe v6))
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
                                 (coe v6))
                              (coe v8) (coe v9) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
