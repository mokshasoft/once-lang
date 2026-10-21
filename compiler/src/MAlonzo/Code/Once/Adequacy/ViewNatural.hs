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
import qualified MAlonzo.Code.Once.Internal.Core.PolyTy
import qualified MAlonzo.Code.Once.Internal.Elaboration
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed

-- Once.Adequacy.ViewNatural._.ImportAt
d_ImportAt_14 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.ViewNatural._.View
d_View_18 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ViewNatural._.ImportAt.entryOf
d_entryOf_26 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entryOf_26 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_entryOf_504 (coe v0)
-- Once.Adequacy.ViewNatural._.ImportAt.instOf
d_instOf_28 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instOf_28 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_instOf_506 (coe v0)
-- Once.Adequacy.ViewNatural._.View.declares
d_declares_32 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_Declared_470
d_declares_32 v0
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.d_declares_584 (coe v0)
-- Once.Adequacy.ViewNatural._.View.entry
d_entry_34 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_34 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_entry_594 (coe v0)
-- Once.Adequacy.ViewNatural._.View.ground
d_ground_36 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground_36 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_ground_608 (coe v0)
-- Once.Adequacy.ViewNatural._.View.imported
d_imported_38 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494
d_imported_38 v0
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.d_imported_578 (coe v0)
-- Once.Adequacy.ViewNatural._.View.inst
d_inst_40 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst_40 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_inst_622 (coe v0)
-- Once.Adequacy.ViewNatural._.NatImp
d_NatImp_58 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494 -> ()
d_NatImp_58 = erased
-- Once.Adequacy.ViewNatural._.Natural
d_Natural_74 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_Natural_74 = C_constructor_172
-- Once.Adequacy.ViewNatural._.Natural.nat-inst
d_nat'45'inst_146 ::
  T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'inst_146 = erased
-- Once.Adequacy.ViewNatural._.Natural.nat-ground
d_nat'45'ground_162 ::
  T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'ground_162 = erased
-- Once.Adequacy.ViewNatural._.Natural.nat-imp
d_nat'45'imp_170 ::
  T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'imp_170 = erased
