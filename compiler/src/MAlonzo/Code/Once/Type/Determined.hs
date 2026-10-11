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

module MAlonzo.Code.Once.Type.Determined where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Relation.Binary.Subset.DecSetoid
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.Poly
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Type.Determined.agree-on
d_agree'45'on_14 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'on_14 = erased
-- Once.Type.Determined.agreeF-on
d_agreeF'45'on_24 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyFunctor_8 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agreeF'45'on_24 = erased
-- Once.Type.Determined.*-inj
d_'42''45'inj_194 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'inj_194 ~v0 ~v1 ~v2 ~v3 ~v4 = du_'42''45'inj_194
du_'42''45'inj_194 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'42''45'inj_194
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Type.Determined.+-inj
d_'43''45'inj_204 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inj_204 ~v0 ~v1 ~v2 ~v3 ~v4 = du_'43''45'inj_204
du_'43''45'inj_204 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'43''45'inj_204
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Type.Determined.⇒-inj
d_'8658''45'inj_218 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_ArrowKind_38 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_ArrowKind_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8658''45'inj_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8658''45'inj_218
du_'8658''45'inj_218 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8658''45'inj_218
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Type.Determined.μ-inj
d_μ'45'inj_224 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_μ'45'inj_224 = erased
-- Once.Type.Determined.ν-inj
d_ν'45'inj_234 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ν'45'inj_234 = erased
-- Once.Type.Determined.K-inj
d_K'45'inj_240 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_K'45'inj_240 = erased
-- Once.Type.Determined.⊕-inj
d_'8853''45'inj_250 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8853''45'inj_250 ~v0 ~v1 ~v2 ~v3 ~v4 = du_'8853''45'inj_250
du_'8853''45'inj_250 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8853''45'inj_250
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Type.Determined.⊗-inj
d_'8855''45'inj_260 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8855''45'inj_260 ~v0 ~v1 ~v2 ~v3 ~v4 = du_'8855''45'inj_260
du_'8855''45'inj_260 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8855''45'inj_260
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Type.Determined.agree-from
d_agree'45'from_270 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'from_270 = erased
-- Once.Type.Determined.pair-from
d_pair'45'from_282 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'from_282 = erased
-- Once.Type.Determined.agreeF-from
d_agreeF'45'from_292 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agreeF'45'from_292 = erased
-- Once.Type.Determined.pairF-from
d_pairF'45'from_304 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pairF'45'from_304 = erased
-- Once.Type.Determined.cod-determined
d_cod'45'determined_528 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cod'45'determined_528 = erased
-- Once.Type.Determined.codVarsInDom?
d_codVarsInDom'63'_548 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_codVarsInDom'63'_548 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Subset.DecSetoid.du__'8838''63'__40
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
         (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
      (coe MAlonzo.Code.Once.Spec.Type.Poly.d_ftv_226 (coe v1))
      (coe MAlonzo.Code.Once.Spec.Type.Poly.d_ftv_226 (coe v0))
-- Once.Type.Determined.ArrowView
d_ArrowView_554 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 -> ()
d_ArrowView_554 = erased
-- Once.Type.Determined.arrowSchema?
d_arrowSchema'63'_566 ::
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowSchema'63'_566 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.Poly.C_PUnit_20
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.Poly.C_PVoid_22
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'42'__24 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'43'__26 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.Poly.C__P'8658''91'_'93'__28 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Type.Grade.C_One_12
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                             (coe MAlonzo.Code.Once.Spec.Type.Poly.C_as'45'pure_268))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.Poly.C_PEff_30 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32)
                      (coe MAlonzo.Code.Once.Spec.Type.Poly.C_as'45'eff_274))))
      MAlonzo.Code.Once.Spec.Type.Poly.C_Pμ'45'type_32 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.Poly.C_Pν'45'type_34 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.Poly.C_PInt_36
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.Poly.C_PFloat_38
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Spec.Type.Poly.C_PTVar_40 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
