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

module MAlonzo.Code.Once.Adequacy.ViewNatural where

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
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Elaboration
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.ViewNatural._.ImportAt
d_ImportAt_14 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.ViewNatural._.View
d_View_18 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ViewNatural._.ImportAt.entryOf
d_entryOf_26 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_484 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entryOf_26 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_entryOf_494 (coe v0)
-- Once.Adequacy.ViewNatural._.ImportAt.instOf
d_instOf_28 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_484 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instOf_28 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_instOf_496 (coe v0)
-- Once.Adequacy.ViewNatural._.View.declares
d_declares_32 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_Declared_460
d_declares_32 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_declares_574 (coe v0)
-- Once.Adequacy.ViewNatural._.View.entry
d_entry_34 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_34 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_entry_584 (coe v0)
-- Once.Adequacy.ViewNatural._.View.ground
d_ground_36 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground_36 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_ground_598 (coe v0)
-- Once.Adequacy.ViewNatural._.View.imported
d_imported_38 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_484
d_imported_38 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_imported_568 (coe v0)
-- Once.Adequacy.ViewNatural._.View.inst
d_inst_40 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_506 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst_40 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_inst_612 (coe v0)
-- Once.Adequacy.ViewNatural._.NatImp
d_NatImp_58 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_TKind_110) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_484 -> ()
d_NatImp_58 = erased
-- Once.Adequacy.ViewNatural._.Natural
d_Natural_74 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_Natural_74 = C_constructor_172
-- Once.Adequacy.ViewNatural._.Natural.nat-inst
d_nat'45'inst_146 ::
  T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'inst_146 = erased
-- Once.Adequacy.ViewNatural._.Natural.nat-ground
d_nat'45'ground_162 ::
  T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'ground_162 = erased
-- Once.Adequacy.ViewNatural._.Natural.nat-imp
d_nat'45'imp_170 ::
  T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'imp_170 = erased
