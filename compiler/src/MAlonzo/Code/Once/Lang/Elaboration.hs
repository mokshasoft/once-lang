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

module MAlonzo.Code.Once.Lang.Elaboration where

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
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Core.Derived
import qualified MAlonzo.Code.Once.Lang.Core.DerivedTyping
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.Rename
import qualified MAlonzo.Code.Once.Lang.Core.Syntax
import qualified MAlonzo.Code.Once.Lang.Core.Typing
import qualified MAlonzo.Code.Once.Lang.Name
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Lang.Elaboration._.Lit
d_Lit_16 a0 a1 a2 = ()
-- Once.Lang.Elaboration._.Prim
d_Prim_18 a0 a1 a2 = ()
-- Once.Lang.Elaboration._.Tm
d_Tm_24 a0 a1 a2 a3 = ()
-- Once.Lang.Elaboration._.primCod
d_primCod_100 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_primCod_100 ~v0 ~v1 ~v2 = du_primCod_100
du_primCod_100 ::
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_primCod_100
  = coe MAlonzo.Code.Once.Lang.Core.Syntax.du_primCod_58
-- Once.Lang.Elaboration._.primDom
d_primDom_102 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_primDom_102 ~v0 ~v1 ~v2 = du_primDom_102
du_primDom_102 ::
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
du_primDom_102
  = coe MAlonzo.Code.Once.Lang.Core.Syntax.du_primDom_56
-- Once.Lang.Elaboration._._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__246 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Lang.Elaboration.InstanceOf
d_InstanceOf_458 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_InstanceOf_458 = erased
-- Once.Lang.Elaboration.Declared
d_Declared_470 a0 a1 a2 a3 a4 = ()
data T_Declared_470
  = C_declared_488 AgdaAny
                   MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
                   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
-- Once.Lang.Elaboration.Declared.honest
d_honest_482 :: T_Declared_470 -> AgdaAny
d_honest_482 v0
  = case coe v0 of
      C_declared_488 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.Declared.rigid
d_rigid_484 ::
  T_Declared_470 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
d_rigid_484 v0
  = case coe v0 of
      C_declared_488 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.Declared.member
d_member_486 ::
  T_Declared_470 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_member_486 v0
  = case coe v0 of
      C_declared_488 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.ImportAt
d_ImportAt_494 a0 a1 a2 a3 a4 = ()
data T_ImportAt_494
  = C_def_508 MAlonzo.Code.Data.Fin.Base.T_Fin_10
              MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Once.Lang.Elaboration.ImportAt.entryOf
d_entryOf_504 ::
  T_ImportAt_494 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entryOf_504 v0
  = case coe v0 of
      C_def_508 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.ImportAt.instOf
d_instOf_506 ::
  T_ImportAt_494 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instOf_506 v0
  = case coe v0 of
      C_def_508 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.View
d_View_516 a0 a1 a2 a3 a4 a5 = ()
data T_View_516
  = C_constructor_624 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ImportAt_494)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Declared_470)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
                       MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       MAlonzo.Code.Data.Fin.Base.T_Fin_10)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
                       MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                      (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                       MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
                       MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
                       [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                       MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                       MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                       (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                       MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.Lang.Elaboration.View.imported
d_imported_578 ::
  T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_ImportAt_494
d_imported_578 v0
  = case coe v0 of
      C_constructor_624 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.View.declares
d_declares_584 ::
  T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Declared_470
d_declares_584 v0
  = case coe v0 of
      C_constructor_624 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.View.entry
d_entry_594 ::
  T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_594 v0
  = case coe v0 of
      C_constructor_624 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.View.ground
d_ground_608 ::
  T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground_608 v0
  = case coe v0 of
      C_constructor_624 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.View.inst
d_inst_622 ::
  T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst_622 v0
  = case coe v0 of
      C_constructor_624 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.Views
d_Views_626 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 -> ()
d_Views_626 = erased
-- Once.Lang.Elaboration.Elab
d_Elab_632 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_Elab_632 = erased
-- Once.Lang.Elaboration.lift1
d_lift1_664 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lift1_664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_lift1_664 v9 v10 v11
du_lift1_664 ::
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lift1_664 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v3)
             (coe v1 v3 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.lift2
d_lift2_684 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lift2_684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12
            v13 v14
  = du_lift2_684 v11 v12 v13 v14
du_lift2_684 ::
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lift2_684 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v4 v6)
                    (coe v1 v4 v6 v5 v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.appC
d_appC_700 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_appC_700 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 v8 v9
  = du_appC_700 v3 v5 v7 v8 v9
du_appC_700 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_appC_700 v0 v1 v2 v3 v4
  = coe
      du_lift1_664
      (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70 (coe v3))
      (coe
         (\ v5 ->
            coe
              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)) v2
              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v1 v4))
-- Once.Lang.Elaboration.bin
d_bin_708 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bin_708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10
  = du_bin_708 v7 v8 v9
du_bin_708 ::
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin_708 v0 v1 v2
  = coe
      du_lift2_684
      (coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Once.Lang.Core.Syntax.C_prim_104 (coe v2)
              (coe
                 MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76 (coe v3) (coe v4))))
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'prim_608
              (coe
                 MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'pair_354 v0 v1
                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v5 v6)))
-- Once.Lang.Elaboration.i2f
d_i2f_724 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_i2f_724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_i2f_724
du_i2f_724 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_i2f_724
  = coe
      du_lift1_664
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_prim_104
         (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'i2f_54))
      (coe
         (\ v0 -> coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'prim_608))
-- Once.Lang.Elaboration.coerceE
d_coerceE_726 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_coerceE_726 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 v8
  = du_coerceE_726 v3 v4 v8
du_coerceE_726 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'60''58'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_coerceE_726 v0 v1 v2
  = coe
      du_lift1_664
      (coe
         MAlonzo.Code.Once.Lang.Core.Syntax.C_coerce_100 (coe v0) (coe v1))
      (coe
         (\ v3 ->
            coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'coerce_578 v2))
-- Once.Lang.Elaboration.refE
d_refE_736 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refE_736 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_refE_736 v6 v7
du_refE_736 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refE_736 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Syntax.C_ref_110 (coe v0) (coe v2))
                    (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'ref_646 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.sigE
d_sigE_752 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  T_Declared_470 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigE_752 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7 v8
  = du_sigE_752 v3 v6 v7 v8
du_sigE_752 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  T_Declared_470 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigE_752 v0 v1 v2 v3
  = case coe v3 of
      C_declared_488 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Core.Syntax.C_sigop_106 (coe v1) (coe v0))
             (coe
                MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sigop_620 v2 v4 v5 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.sigE⁺
d_sigE'8314'_772 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 ->
  T_Declared_470 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigE'8314'_772 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 v7 v8 v9 v10 v11 v12
  = du_sigE'8314'_772 v3 v4 v7 v8 v9 v10 v11 v12
du_sigE'8314'_772 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_EffGrade_48 ->
  T_Declared_470 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigE'8314'_772 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_declared_488 v8 v9 v10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Core.Syntax.C_sigop_106 (coe v4)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v0)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v2)
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_eff'8314'_38))
                   (coe v1)))
             (coe
                MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sigop'8314'_636 v3 v5 v6
                v8 v9 v10)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.importE
d_importE_794 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_ImportAt_494 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_importE_794 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_importE_794 v7
du_importE_794 ::
  T_ImportAt_494 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_importE_794 v0
  = case coe v0 of
      C_def_508 v1 v2 -> coe du_refE_736 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.closeE
d_closeE_800 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closeE_800 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_closeE_800 v3 v5 v6
du_closeE_800 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_closeE_800 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Lang.Core.Rename.du_close_1008 v3)
             (coe
                MAlonzo.Code.Once.Lang.Core.Rename.du_'8866'close_1020 (coe v1)
                (coe v3) (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.subE
d_subE_806 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subE_806 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 = du_subE_806 v9
du_subE_806 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_subE_806 v0 = coe v0
-- Once.Lang.Elaboration.elabᶜ
d_elab'7580'_818 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  T_View_516 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7580'_818 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'check_442 v12
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Derived.du_id'7580'_264 (coe v13)
                              (coe v17))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v12
                                 (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'check_454 v13
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v17 v18
                      -> case coe v15 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v19 v20
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Derived.du_fst'7580'_280 (coe v17)
                                     (coe v18) (coe v20))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v13
                                        (coe
                                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370 v18
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'check_466 v13
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v14 v15 v16
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v17 v18
                      -> case coe v15 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v19 v20
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Derived.du_snd'7580'_284 (coe v17)
                                     (coe v18) (coe v20))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v13
                                        (coe
                                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386 v17
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'morph'45'check_476 v12
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Derived.du_terminal'7580'_268 (coe v13)
                              (coe v17))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v12
                                 (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'morph'45'check_486 v12
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v16 v17
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                              (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v17)
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.Syntax.C_absurd_88 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v12
                                 (coe
                                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'absurd_462
                                    (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'morph'45'check_498 v13
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v17 v18
                      -> case coe v16 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v19 v20
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Derived.du_inl'7580'_288 (coe v14)
                                     (coe v20) (coe v18))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v13
                                        (coe
                                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inl_402
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'morph'45'check_510 v13
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v17 v18
                      -> case coe v16 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v19 v20
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Derived.du_inr'7580'_292 (coe v19)
                                     (coe v14) (coe v18))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v13
                                        (coe
                                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inr_418
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'g_530 v13 v16 v17 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v22 v23
                      -> case coe v5 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v24 v25 v26
                             -> case coe v25 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v27 v28
                                    -> coe
                                         du_lift2_684
                                         (coe
                                            MAlonzo.Code.Once.Lang.Core.Derived.du_compose'7580'_348
                                            (coe v24) (coe v28))
                                         (coe
                                            (\ v29 v30 ->
                                               coe
                                                 MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'compose'7580'_600
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                    (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                                    (coe v3))
                                                 (coe v16) (coe v17) (coe v24) (coe v13) (coe v26)
                                                 (coe v28) (coe v28) (coe v30)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.Sub.d_'183'p'45'diag_28
                                                    (coe v28))))
                                         (coe
                                            d_elab'7580'_818 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v23)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v28))
                                               (coe v26))
                                            (coe v16) (coe v7) (coe v19))
                                         (coe
                                            d_elab'7496'_842 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v21) (coe v24) (coe v13) (coe v28) (coe v17)
                                            (coe v7) (coe v18))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'compose'45'check'45'f_554 v13 v15 v17 v18 v19 v20 v21 v22
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v23 v24
               -> case coe v23 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v25 v26
                      -> case coe v5 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v27 v28 v29
                             -> case coe v28 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v30 v31
                                    -> coe
                                         du_lift2_684
                                         (coe
                                            MAlonzo.Code.Once.Lang.Core.Derived.du_compose'7580'_348
                                            (coe v27) (coe v31))
                                         (coe
                                            (\ v32 v33 ->
                                               coe
                                                 MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'compose'7580'_600
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                    (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                                    (coe v3))
                                                 (coe v18) (coe v19) (coe v27) (coe v13) (coe v29)
                                                 (coe v31) (coe v31) (coe v33)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.Sub.d_'183'p'45'diag_28
                                                    (coe v31))))
                                         (coe
                                            du_coerceE_726
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v17))
                                               (coe v15))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v13)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v31))
                                               (coe v29))
                                            v21
                                            (d_elab'7522'_828
                                               (coe v0) (coe v1) (coe v2) (coe v3) (coe v26)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                     (coe v17))
                                                  (coe v15))
                                               (coe v18) (coe v7) (coe v20)))
                                         (coe
                                            d_elab'7580'_818 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v24)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v27)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v31))
                                               (coe v13))
                                            (coe v19) (coe v7) (coe v22))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case'45'copair'45'check_574 v16 v17 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v22 v23
                      -> case coe v5 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v24 v25 v26
                             -> case coe v24 of
                                  MAlonzo.Code.Once.Lang.Type.C__'43'__26 v27 v28
                                    -> case coe v25 of
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v29 v30
                                           -> coe
                                                du_lift2_684
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Core.Derived.du_case'7580'_372
                                                   (coe v27) (coe v28) (coe v30))
                                                (\ v31 v32 v33 v34 ->
                                                   coe
                                                     MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'case'7580'_688
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                        (coe v3))
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                                        (coe v3))
                                                     (coe v16) (coe v17) (coe v27) (coe v28)
                                                     (coe v26) (coe v30) v32 v33 v34)
                                                (coe
                                                   d_elab'7580'_818 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v23)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v27)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v30))
                                                      (coe v26))
                                                   (coe v16) (coe v7) (coe v18))
                                                (coe
                                                   d_elab'7580'_818 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v21)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v28)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v30))
                                                      (coe v26))
                                                   (coe v17) (coe v7) (coe v19))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'morph'45'check_594 v16 v17 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v22 v23
                      -> case coe v5 of
                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v24 v25 v26
                             -> case coe v25 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v27 v28
                                    -> case coe v26 of
                                         MAlonzo.Code.Once.Lang.Type.C__'42'__24 v29 v30
                                           -> coe
                                                du_lift2_684
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Core.Derived.du_pair'7580'_360
                                                   (coe v24) (coe v28))
                                                (coe
                                                   (\ v31 v32 ->
                                                      coe
                                                        MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'pair'7580'_650
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                           (coe v3))
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                                           (coe v3))
                                                        (coe v16) (coe v17) (coe v24) (coe v29)
                                                        (coe v30) (coe v28) (coe v28) (coe v32)
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Type.Sub.d_'183'p'45'diag_28
                                                           (coe v28))))
                                                (coe
                                                   d_elab'7580'_818 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v23)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v24)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v28))
                                                      (coe v29))
                                                   (coe v16) (coe v7) (coe v18))
                                                (coe
                                                   d_elab'7580'_818 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v21)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe v24)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v28))
                                                      (coe v30))
                                                   (coe v17) (coe v7) (coe v19))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'curry'45'check_614 v17 v18
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v19 v20
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v21 v22 v23
                      -> case coe v22 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v24 v25
                             -> case coe v23 of
                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v26 v27 v28
                                    -> case coe v27 of
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v29 v30
                                           -> coe
                                                du_lift1_664
                                                (coe
                                                   (\ v31 ->
                                                      coe
                                                        MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                                                        (coe v31)
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                                                           (coe v21)
                                                           (coe
                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                           (coe v25)
                                                           (coe
                                                              MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                                                              (coe v26)
                                                              (coe
                                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                              (coe v30)
                                                              (coe
                                                                 MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
                                                                 (coe
                                                                    MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                                                    (coe
                                                                       MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                       (coe
                                                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                          (coe
                                                                             MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76
                                                                    (coe
                                                                       MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                                                       (coe
                                                                          MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                          (coe
                                                                             MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                                                    (coe
                                                                       MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                                                       (coe
                                                                          MAlonzo.Code.Data.Fin.Base.C_zero_12))))))))
                                                (coe
                                                   (\ v31 ->
                                                      coe
                                                        MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'curry'7580'_726
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                           (coe v3))
                                                        (coe v6) (coe v21) (coe v26) (coe v28)
                                                        (coe v30) (coe v17)))
                                                (coe
                                                   d_elab'7580'_818 (coe v0) (coe v1) (coe v2)
                                                   (coe v3) (coe v20)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                         (coe v21) (coe v26))
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                         (coe
                                                            MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                         (coe v30))
                                                      (coe v28))
                                                   (coe v6) (coe v7) (coe v18))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'cata'45'check_630 v14 v15 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                      -> case coe v20 of
                           MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v23
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v24 v25
                                    -> coe
                                         du_lift1_664
                                         (coe
                                            (\ v26 ->
                                               coe
                                                 MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72
                                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                 (coe v26)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                                                    (coe v20)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                    (coe v25)
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Core.Syntax.C_fold_92
                                                       (coe v23)
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                                          (coe
                                                             MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                             (coe
                                                                MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                                       (coe
                                                          MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                                          (coe
                                                             MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
                                         (coe
                                            (\ v26 ->
                                               coe
                                                 MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'cata'7580'_760
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                    (coe v3))
                                                 (coe v14) (coe v23) (coe v22) (coe v25) (coe v15)
                                                 (coe v16)))
                                         (coe
                                            d_elab'7580'_818 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v19)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                  (coe v23) (coe v22))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v25))
                                               (coe v22))
                                            (coe v14) (coe v7) (coe v17))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'ana'45'check_648 v15 v16 v17 v18
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v19 v20
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v21 v22 v23
                      -> case coe v22 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v24 v25
                             -> case coe v23 of
                                  MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v26 v27
                                    -> coe
                                         du_lift1_664
                                         (coe
                                            MAlonzo.Code.Once.Lang.Core.Derived.du_ana'7580'_410
                                            (coe v26) (coe v21) (coe v25))
                                         (coe
                                            (\ v28 ->
                                               coe
                                                 MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'ana'7580'_796
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                    (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                                    (coe v3))
                                                 (coe v15) (coe v26) (coe v21) (coe v27) (coe v28)
                                                 (coe v16) (coe v17)))
                                         (coe
                                            d_elab'7580'_818 (coe v0) (coe v1) (coe v2) (coe v3)
                                            (coe v20)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                               (coe v21)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v27))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                                  (coe v26) (coe v21)))
                                            (coe v15) (coe v7) (coe v18))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'sub_660 v11 v14 v15
        -> coe
             du_coerceE_726 v11 v5 v15
             (d_elab'7522'_828
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v11) (coe v6)
                (coe v7) (coe v14))
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved'45'guard_674 v14 v15 v17 v18
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v19
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v23 v24
                             -> coe
                                  du_sigE'8314'_772 (coe v20) (coe v22) (coe v23) (coe v14)
                                  (coe v19) (coe v18) (coe v17)
                                  (coe
                                     d_declares_584 v7
                                     (MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v19))
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v20)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                           (coe v23) (coe v14))
                                        (coe v22))
                                     erased)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'lam_696 v15 v18 v20
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v21 v22
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v23 v24 v25
                      -> case coe v24 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v26 v27
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v23) (coe v26)
                                     (coe v27)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                        (coe
                                           d_elab'7580'_818 (coe v0) (coe v1) (coe v2)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                              (coe
                                                 addInt (coe (1 :: Integer))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                    (coe v3)))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120
                                                    (coe v3))
                                                 (coe v21) (coe v23))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                                 (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                                    (coe v3))
                                                 v23
                                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124
                                                 (coe v3))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126
                                                 (coe v3))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128
                                                 (coe v3)))
                                           (coe v22) (coe v25)
                                           (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v15 v6)
                                           (coe v7) (coe v20))))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276 v15
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v18
                                        (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              d_elab'7580'_818 (coe v0) (coe v1) (coe v2)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                                 (coe
                                                    addInt (coe (1 :: Integer))
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                       (coe v3)))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120
                                                       (coe v3))
                                                    (coe v21) (coe v23))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                                    (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                                       (coe v3))
                                                    v23
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124
                                                    (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126
                                                    (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128
                                                    (coe v3)))
                                              (coe v22) (coe v25)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v15
                                                 v6)
                                              (coe v7) (coe v20)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair'45'lit'45'check_712 v14 v15 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v18 v19
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v20 v21
                      -> coe
                           du_lift2_684 (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76)
                           (\ v22 v23 v24 v25 ->
                              coe
                                MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'pair_354 v14 v15
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v24 v25)
                           (coe
                              d_elab'7580'_818 (coe v0) (coe v1) (coe v2) (coe v3) (coe v18)
                              (coe v20) (coe v14) (coe v7) (coe v16))
                           (coe
                              d_elab'7580'_818 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe v21) (coe v15) (coe v7) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'In'45'app'45'check_722 v12 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v17
                      -> coe
                           du_appC_700
                           (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                           (MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                              (coe v17) (coe v5))
                           v12
                           (coe MAlonzo.Code.Once.Lang.Core.Derived.du_in'7580'_336 (coe v17))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'roll_476 v13
                                 (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
                           (d_elab'7580'_818
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v17)
                                 (coe v5))
                              (coe v12) (coe v7) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'check_734 v11 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> coe
                    du_appC_700
                    (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                    (coe
                       MAlonzo.Code.Once.Lang.Type.C__'42'__24
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v5))
                       (coe v11))
                    v13
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'42'__24
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v5))
                          (coe v11))
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
                          (coe
                             MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78
                             (coe
                                MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                          (coe
                             MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80
                             (coe
                                MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'apply'7580'_822
                       (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                       (coe v11) (coe v5))
                    (d_elab'7522'_828
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'42'__24
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v5))
                          (coe v11))
                       (coe v13) (coe v7) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inl'45'app'45'check_746 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v17 v18
                      -> coe
                           du_appC_700
                           (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)) v17 v13
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Derived.du_inl'7580'_288 (coe v17)
                              (coe v18) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                                 (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inl_402
                                    (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
                           (d_elab'7580'_818
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v16) (coe v17) (coe v13)
                              (coe v7) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'inr'45'app'45'check_758 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v17 v18
                      -> coe
                           du_appC_700
                           (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)) v18 v13
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Derived.du_inr'7580'_292 (coe v17)
                              (coe v18) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                                 (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inr_418
                                    (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
                           (d_elab'7580'_818
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v16) (coe v18) (coe v13)
                              (coe v7) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'initial'45'app'45'check_768 v12 v13
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v14 v15
               -> coe
                    du_appC_700
                    (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                    (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) v12
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                       (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Syntax.C_absurd_88 (coe v5)
                          (coe
                             MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                          (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10)
                          (coe
                             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'absurd_462
                             (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
                    (d_elab'7580'_818
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v12) (coe v7)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate_782 v12 v13 v14 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v20
               -> coe
                    du_refE_736 (coe d_entry_594 v7 v20 v12 v13 v14 erased)
                    (coe d_inst_622 v7 v20 v12 v13 v14 v5 erased erased v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.elabᵢ
d_elab'7522'_828 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  T_View_516 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7522'_828 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'int_30
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v11
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Syntax.C_lit_102
                       (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_lit'45'int_16 (coe v11)))
                    (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'int_586)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'float_42
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v14 v15 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Syntax.C_lit_102
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Syntax.C_lit'45'float_18
                          (coe
                             MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v14)
                             (coe v15) (coe v16))))
                    (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'float_594)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit_46
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_unit_74)
             (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_unit_74)
             (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62 v13
        -> case coe v13 of
             MAlonzo.Code.Once.Lang.Context.C_svar_120 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66 (coe v17))
                    (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'qualified_72 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RQualified_38 v15 v16
               -> coe
                    du_sigE_752 (coe v5)
                    (coe
                       MAlonzo.Code.Once.Spec.Name.d_bare_14
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v16
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                             ("." :: Data.Text.Text) v15)))
                    (coe v14)
                    (coe
                       d_declares_584 v7
                       (MAlonzo.Code.Once.Lang.Name.d_showCanonical_6
                          (coe
                             MAlonzo.Code.Once.Spec.Name.d_bare_14
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20 v16
                                (coe
                                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                   ("." :: Data.Text.Text) v15))))
                       v5 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v12 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v15
               -> coe
                    du_sigE_752 (coe v5) (coe v15) (coe v14)
                    (coe
                       d_declares_584 v7
                       (MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v15)) v5
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v15
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v16
                      -> case coe v16 of
                           (:) v17 v18
                             -> coe du_importE_794 (coe d_imported_578 v7 v17 v5 erased)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_96 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v16
               -> coe du_importE_794 (coe d_imported_578 v7 v16 v5 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_112 v12 v13 v14 v15 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v21
               -> coe
                    du_refE_736 (coe d_entry_594 v7 v21 v12 v13 v14 erased)
                    (coe d_ground_608 v7 v21 v12 v13 v14 erased v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'annot_122 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_60 v15 v16
               -> coe
                    d_elab'7580'_818 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                    (coe v5) (coe v6) (coe v7) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_138 v14 v15 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v18 v19
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v20 v21
                      -> coe
                           du_lift2_684 (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76)
                           (\ v22 v23 v24 v25 ->
                              coe
                                MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'pair_354 v14 v15
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v24 v25)
                           (coe
                              d_elab'7522'_828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v18)
                              (coe v20) (coe v14) (coe v7) (coe v16))
                           (coe
                              d_elab'7522'_828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe v21) (coe v15) (coe v7) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg_146 v12
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64 v14
               -> coe
                    du_lift1_664
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Syntax.C_prim_104
                       (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'neg_32))
                    (coe
                       (\ v15 -> coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'prim_608))
                    (coe
                       d_elab'7522'_828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v14)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v6) (coe v7)
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg'45'float_158
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64 v15
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v16 v17 v18 v19
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Syntax.C_lit_102
                              (coe
                                 MAlonzo.Code.Once.Lang.Core.Syntax.C_lit'45'float_18
                                 (coe
                                    MAlonzo.Code.Once.Spec.Float.Decimal.d_negate_24
                                    (coe
                                       MAlonzo.Code.Once.Spec.Float.Decimal.d_decimalOf_30 (coe v16)
                                       (coe v17) (coe v18)))))
                           (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'float_594)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'let_178 v13 v15 v16 v17 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v20 v21 v22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72 (coe v15)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                             (coe v13) (coe v16) (coe v7) (coe v18)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_828 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v3))
                                   (coe v20) (coe v13))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                   (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v3)) v13
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v3)))
                             (coe v22) (coe v5)
                             (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v15 v17) (coe v7)
                             (coe v19))))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Typing.du_'8866'let'45'pure_762
                       (coe v16) (coe v17)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) (coe v13)
                       (coe v15)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_elab'7522'_828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                             (coe v13) (coe v16) (coe v7) (coe v18)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_elab'7522'_828 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v3))
                                   (coe v20) (coe v13))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                   (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v3)) v13
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v3)))
                             (coe v22) (coe v5)
                             (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v15 v17) (coe v7)
                             (coe v19))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case_208 v15 v16 v18 v19 v20 v21 v22 v23 v24 v25
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v26 v27 v28 v29 v30
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Syntax.C_case_86 (coe v18) (coe v19)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v26)
                             (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v15) (coe v16))
                             (coe v20) (coe v7) (coe v23)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_828 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v3))
                                   (coe v27) (coe v15))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                   (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v3)) v15
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v3)))
                             (coe v28) (coe v5)
                             (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v18 v21) (coe v7)
                             (coe v24)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_828 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v3))
                                   (coe v29) (coe v16))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                   (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v3)) v16
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v3)))
                             (coe v30) (coe v5)
                             (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v19 v22) (coe v7)
                             (coe v25))))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Typing.du_'8866'case'8852'_726
                       (coe v20) (coe v21) (coe v22) (coe v18) (coe v19)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) (coe v15)
                       (coe v16)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_elab'7522'_828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v26)
                             (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v15) (coe v16))
                             (coe v20) (coe v7) (coe v23)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_elab'7522'_828 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v3))
                                   (coe v27) (coe v15))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                   (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v3)) v15
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v3)))
                             (coe v28) (coe v5)
                             (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v18 v21) (coe v7)
                             (coe v24)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe
                             d_elab'7522'_828 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v3))
                                   (coe v29) (coe v16))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                   (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v3)) v16
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v3)))
                             (coe v30) (coe v5)
                             (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v19 v22) (coe v7)
                             (coe v25))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_222 v13 v14 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'add_22)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'sub_24)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'mul_26)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'div_28)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpMod_16
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'mod_30)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float_236 v13 v14 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fadd_46)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fsub_48)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fmul_50)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fdiv_52)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v14) (coe v7)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'il_250 v13 v14 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fadd_46)
                           (coe
                              du_i2f_724
                              (d_elab'7522'_828
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                                 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                                 (coe v16)))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fsub_48)
                           (coe
                              du_i2f_724
                              (d_elab'7522'_828
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                                 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                                 (coe v16)))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fmul_50)
                           (coe
                              du_i2f_724
                              (d_elab'7522'_828
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                                 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                                 (coe v16)))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fdiv_52)
                           (coe
                              du_i2f_724
                              (d_elab'7522'_828
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                                 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                                 (coe v16)))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v14) (coe v7)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'ir_264 v13 v14 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Syntax.C_OpAdd_8
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fadd_46)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v13) (coe v7)
                              (coe v16))
                           (coe
                              du_i2f_724
                              (d_elab'7522'_828
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                                 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                                 (coe v17)))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpSub_10
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fsub_48)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v13) (coe v7)
                              (coe v16))
                           (coe
                              du_i2f_724
                              (d_elab'7522'_828
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                                 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                                 (coe v17)))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpMul_12
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fmul_50)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v13) (coe v7)
                              (coe v16))
                           (coe
                              du_i2f_724
                              (d_elab'7522'_828
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                                 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                                 (coe v17)))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpDiv_14
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'fdiv_52)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v13) (coe v7)
                              (coe v16))
                           (coe
                              du_i2f_724
                              (d_elab'7522'_828
                                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                                 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                                 (coe v17)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_278 v13 v14 v16 v17
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Syntax.C_OpLt_18
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'lt_34)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpLe_20
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'le_36)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpGt_22
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'gt_38)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpGe_24
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'ge_40)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpEq_26
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'eq_42)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                              (coe v17))
                    MAlonzo.Code.Once.Lang.Syntax.C_OpNe_28
                      -> coe
                           du_bin_708 v13 v14
                           (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_p'45'ne_44)
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v7)
                              (coe v16))
                           (d_elab'7522'_828
                              (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14) (coe v7)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_288 v12 v13
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v14 v15
               -> coe
                    du_appC_700
                    (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)) v5 v12
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Derived.du_id'7580'_264 (coe v5)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                          (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10)
                          (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
                    (d_elab'7522'_828
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v15) (coe v5) (coe v12)
                       (coe v7) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'app_300 v12 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> coe
                    du_appC_700
                    (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                    (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v5) (coe v12))
                    v13
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Derived.du_fst'7580'_280 (coe v5)
                       (coe v12) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                          (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10)
                          (coe
                             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370 v12
                             (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
                    (d_elab'7522'_828
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v5) (coe v12))
                       (coe v13) (coe v7) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'app_312 v11 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> coe
                    du_appC_700
                    (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                    (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v11) (coe v5))
                    v13
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Derived.du_snd'7580'_284 (coe v11)
                       (coe v5) (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                          (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10)
                          (coe
                             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386 v11
                             (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
                    (d_elab'7522'_828
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v11) (coe v5))
                       (coe v13) (coe v7) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_322 v11 v12 v13
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v14 v15
               -> coe
                    du_appC_700
                    (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)) v11 v12
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Derived.du_terminal'7580'_268 (coe v11)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                          (coe MAlonzo.Code.Once.Lang.Type.Sub.C_'8849''45'pure_10)
                          (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332)))
                    (d_elab'7522'_828
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v15) (coe v11) (coe v12)
                       (coe v7) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_334 v11 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v15 v16
               -> coe
                    du_appC_700
                    (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                    (coe
                       MAlonzo.Code.Once.Lang.Type.C__'42'__24
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v5))
                       (coe v11))
                    v13
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'42'__24
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v5))
                          (coe v11))
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
                          (coe
                             MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78
                             (coe
                                MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                          (coe
                             MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80
                             (coe
                                MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'apply'7580'_822
                       (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                       (coe v11) (coe v5))
                    (d_elab'7522'_828
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'42'__24
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                             (coe v5))
                          (coe v11))
                       (coe v13) (coe v7) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_350 v11 v13 v15 v16
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v22 v23
                             -> coe
                                  du_appC_700
                                  (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v23))
                                        (coe v21))
                                     (coe v11))
                                  v13
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                           (coe v11)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe v23))
                                           (coe v21))
                                        (coe v11))
                                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                                        (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v23)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                                 (coe
                                                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                                 (coe
                                                    MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'applyEff'7580'_858
                                     (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                                     (coe v23) (coe v11) (coe v21))
                                  (d_elab'7522'_828
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v18)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                           (coe v11)
                                           (coe
                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                              (coe v23))
                                           (coe v21))
                                        (coe v11))
                                     (coe v13) (coe v7) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_362 v11 v13 v14 v16
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
               -> coe
                    du_appC_700
                    (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                    (coe
                       MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v11)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                    v13
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Derived.du_out'7580'_340 (coe v11))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'out_540
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v11 v14
                          (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
                    (d_elab'7522'_828
                       (coe v0) (coe v1) (coe v2) (coe v3) (coe v18)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v11)
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                       (coe v13) (coe v7) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_378 v11 v13 v15 v16 v18
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v19 v20
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v21 v22 v23
                      -> case coe v22 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v24 v25
                             -> coe
                                  du_appC_700
                                  (MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v11) (coe v25))
                                  v13
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v11)
                                        (coe v25))
                                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                                        (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v25)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Core.Syntax.C_out_98
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                              (coe
                                                 MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'out_540 v25
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v11 v16
                                           (coe
                                              MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
                                  (d_elab'7522'_828
                                     (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v11)
                                        (coe v25))
                                     (coe v13) (coe v7) (coe v18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app_396 v12 v14 v15 v16 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> coe
                    du_lift2_684 (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70)
                    (coe
                       (\ v22 v23 ->
                          coe
                            MAlonzo.Code.Once.Lang.Core.Typing.du_'8866'app'45'pure_796
                            (coe v15) (coe v16)
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) (coe v12)
                            (coe v14)))
                    (coe
                       d_elab'7522'_828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v12)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v14)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v5))
                       (coe v15) (coe v7) (coe v18))
                    (coe
                       d_elab'7580'_818 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                       (coe v12) (coe v16) (coe v7) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_416 v12 v14 v15 v17 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v23 v24 v25
                      -> case coe v24 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v26 v27
                             -> coe
                                  du_lift2_684
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Derived.du_effApp'7580'_422
                                     (coe v27))
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'effApp'7580'_894
                                     (coe
                                        MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v3))
                                     (coe v14) (coe v15) (coe v27) (coe v12) (coe v25))
                                  (coe
                                     d_elab'7522'_828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v12)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v27))
                                        (coe v25))
                                     (coe v14) (coe v7) (coe v19))
                                  (coe
                                     d_elab'7580'_818 (coe v0) (coe v1) (coe v2) (coe v3) (coe v22)
                                     (coe v12) (coe v15) (coe v7) (coe v20))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_432 v12 v14 v15 v17 v18
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v19 v20
               -> coe
                    du_lift2_684 (coe MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70)
                    (\ v21 v22 v23 v24 ->
                       coe
                         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302 v14 v15
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v12 v23 v24)
                    (coe
                       d_elab'7496'_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                       (coe v12) (coe v5)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) (coe v14)
                       (coe v7) (coe v18))
                    (coe
                       d_elab'7522'_828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                       (coe v12) (coe v15) (coe v7) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Elaboration.elabᵈ
d_elab'7496'_842 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  T_View_516 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7496'_842 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = case coe v10 of
      MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_800 v14 v17 v19 v20 v21
        -> coe
             du_coerceE_726
             (coe
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v14)
                (coe
                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v17))
                (coe v6))
             (coe
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
                (coe
                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
                (coe v6))
             (coe
                MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56 v20
                (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_102 (coe v6))
                v21)
             (d_elab'7522'_828
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v14)
                   (coe
                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v17))
                   (coe v6))
                (coe v8) (coe v9) (coe v19))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_824 v16 v17 v18 v19 v20 v21 v26 v27 v28 v29
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v30
               -> coe
                    du_coerceE_726
                    (coe
                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v16))
                       (coe v6))
                    (coe
                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
                       (coe v6))
                    (coe
                       MAlonzo.Code.Once.Lang.Type.Sub.C_sub'45'arr_56
                       (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_102 (coe v5))
                       (MAlonzo.Code.Once.Lang.Type.Sub.d_'60''58''45'refl_102 (coe v6))
                       v29)
                    (coe
                       du_refE_736 (coe d_entry_594 v9 v30 v17 v20 v21 erased)
                       (coe
                          d_inst_622 v9 v30 v17 v20 v21
                          (coe
                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
                             (coe
                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v16))
                             (coe v6))
                          erased erased v28))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_844 v16 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v21 v22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v5)
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             d_elab'7522'_828 (coe v0) (coe v1) (coe v2)
                             (coe
                                MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v3))
                                   (coe v21) (coe v5))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                   (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v3)) v5
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v3))
                                (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v3)))
                             (coe v22) (coe v6)
                             (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v16 v8) (coe v9)
                             (coe v20))))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276 v16
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v19
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                d_elab'7522'_828 (coe v0) (coe v1) (coe v2)
                                (coe
                                   MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                   (coe
                                      addInt (coe (1 :: Integer))
                                      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3)))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Typing.Scope.d_extendCtx_26
                                      (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120 (coe v3))
                                      (coe v21) (coe v5))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                      (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v3))
                                      v5 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124 (coe v3))
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126 (coe v3))
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128 (coe v3)))
                                (coe v22) (coe v6)
                                (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v16 v8) (coe v9)
                                (coe v20)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_864 v15 v18 v19 v20 v21
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v24 v25
                      -> coe
                           du_lift2_684
                           (coe
                              MAlonzo.Code.Once.Lang.Core.Derived.du_compose'7580'_348 (coe v5)
                              (coe v7))
                           (coe
                              (\ v26 v27 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'compose'7580'_600
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v3))
                                   (coe v18) (coe v19) (coe v5) (coe v15) (coe v6) (coe v7) (coe v7)
                                   (coe v27)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.Sub.d_'183'p'45'diag_28
                                      (coe v7))))
                           (coe
                              d_elab'7496'_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v25)
                              (coe v15) (coe v6) (coe v7) (coe v18) (coe v9) (coe v21))
                           (coe
                              d_elab'7496'_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v23)
                              (coe v5) (coe v15) (coe v7) (coe v19) (coe v9) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'id_874 v14
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Core.Derived.du_id'7580'_264 (coe v5)
                (coe v7))
             (coe
                MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                (coe
                   MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v14
                   (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_886 v15
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Derived.du_fst'7580'_280 (coe v6)
                       (coe v17) (coe v7))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v15
                          (coe
                             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370 v17
                             (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_898 v15
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v16 v17
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Derived.du_snd'7580'_284 (coe v16)
                       (coe v6) (coe v7))
                    (coe
                       MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                       (coe
                          MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v15
                          (coe
                             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386 v16
                             (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_908 v14
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Core.Derived.du_terminal'7580'_268 (coe v5)
                (coe v7))
             (coe
                MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                (coe
                   MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v14
                   (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332)))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_916 v13
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68
                (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7)
                (coe
                   MAlonzo.Code.Once.Lang.Core.Syntax.C_absurd_88
                   (coe MAlonzo.Code.Once.Lang.Type.C_Void_22)
                   (coe
                      MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
             (coe
                MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
                (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                (coe
                   MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v13
                   (coe
                      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'absurd_462
                      (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
      MAlonzo.Code.Once.Lang.Typing.C_d'45'case_936 v18 v19 v20 v21
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v24 v25
                      -> case coe v5 of
                           MAlonzo.Code.Once.Lang.Type.C__'43'__26 v26 v27
                             -> coe
                                  du_lift2_684
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Derived.du_case'7580'_372 (coe v26)
                                     (coe v27) (coe v7))
                                  (\ v28 v29 v30 v31 ->
                                     coe
                                       MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'case'7580'_688
                                       (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                                       (coe
                                          MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                          (coe v3))
                                       (coe v18) (coe v19) (coe v26) (coe v27) (coe v6) (coe v7) v29
                                       v30 v31)
                                  (coe
                                     d_elab'7496'_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v25)
                                     (coe v26) (coe v6) (coe v7) (coe v18) (coe v9) (coe v20))
                                  (coe
                                     d_elab'7496'_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v23)
                                     (coe v27) (coe v6) (coe v7) (coe v19) (coe v9) (coe v21))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_956 v18 v19 v20 v21
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v24 v25
                      -> case coe v6 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v26 v27
                             -> coe
                                  du_lift2_684
                                  (coe
                                     MAlonzo.Code.Once.Lang.Core.Derived.du_pair'7580'_360 (coe v5)
                                     (coe v7))
                                  (coe
                                     (\ v28 v29 ->
                                        coe
                                          MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'pair'7580'_650
                                          (coe
                                             MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                             (coe v3))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                             (coe v3))
                                          (coe v18) (coe v19) (coe v5) (coe v26) (coe v27) (coe v7)
                                          (coe v7) (coe v29)
                                          (coe
                                             MAlonzo.Code.Once.Lang.Type.Sub.d_'183'p'45'diag_28
                                             (coe v7))))
                                  (coe
                                     d_elab'7496'_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v25)
                                     (coe v5) (coe v26) (coe v7) (coe v18) (coe v9) (coe v20))
                                  (coe
                                     d_elab'7496'_842 (coe v0) (coe v1) (coe v2) (coe v3) (coe v23)
                                     (coe v5) (coe v27) (coe v7) (coe v19) (coe v9) (coe v21))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_972 v16 v17 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v20 v21
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v22
                      -> coe
                           du_lift1_664
                           (coe
                              (\ v23 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72
                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v23)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 (coe v5)
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Core.Syntax.C_fold_92 (coe v22)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                            (coe
                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                         (coe
                                            MAlonzo.Code.Once.Lang.Core.Syntax.C_var_66
                                            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
                           (coe
                              (\ v23 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'cata'7580'_760
                                   (coe MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118 (coe v3))
                                   (coe v16) (coe v22) (coe v6) (coe v7) (coe v17) (coe v18)))
                           (coe
                              d_elab'7522'_828 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v22)
                                    (coe v6))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
                                 (coe v6))
                              (coe v16) (coe v9) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
