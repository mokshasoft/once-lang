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

module MAlonzo.Code.Once.Type.Rigid where

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
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Instance
import qualified MAlonzo.Code.Once.Type.Match
import qualified MAlonzo.Code.Once.Type.MatchCorrect
import qualified MAlonzo.Code.Once.Type.Poly
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Type.Rigid.subst-ground
d_subst'45'ground_14 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'ground_14 = erased
-- Once.Type.Rigid.subst-groundF
d_subst'45'groundF_24 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'groundF_24 = erased
-- Once.Type.Rigid.++-⊥
d_'43''43''45''8869'_150 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''43''45''8869'_150 = erased
-- Once.Type.Rigid.ftv-ground
d_ftv'45'ground_194 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftv'45'ground_194 = erased
-- Once.Type.Rigid.ftvF-ground
d_ftvF'45'ground_200 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftvF'45'ground_200 = erased
-- Once.Type.Rigid.ftvK-ground
d_ftvK'45'ground_274 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftvK'45'ground_274 = erased
-- Once.Type.Rigid.ftvKF-ground
d_ftvKF'45'ground_280 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftvKF'45'ground_280 = erased
-- Once.Type.Rigid.ground-kinded
d_ground'45'kinded_358 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground'45'kinded_358 ~v0 ~v1 ~v2 ~v3 = du_ground'45'kinded_358
du_ground'45'kinded_358 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ground'45'kinded_358
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            (\ v0 v1 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
-- Once.Type.Rigid.ftvK⊆ftv
d_ftvK'8838'ftv_372 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_ftvK'8838'ftv_372 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28 v3 v4
        -> coe
             du_'43''43''45'mono_394 (coe v1)
             (coe MAlonzo.Code.Once.Type.Instance.d_ftvK_6 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v4))
             (coe d_ftvK'8838'ftv_372 (coe v3))
             (coe d_ftvK'8838'ftv_372 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v3 v4
        -> coe
             du_'43''43''45'mono_394 (coe v1)
             (coe MAlonzo.Code.Once.Type.Instance.d_ftvK_6 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v4))
             (coe d_ftvK'8838'ftv_372 (coe v3))
             (coe d_ftvK'8838'ftv_372 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v3 v4 v5
        -> coe
             du_'43''43''45'mono_394 (coe v1)
             (coe MAlonzo.Code.Once.Type.Instance.d_ftvK_6 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v5))
             (coe d_ftvK'8838'ftv_372 (coe v3))
             (coe d_ftvK'8838'ftv_372 (coe v5)) (coe v2)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v3 v4
        -> coe
             du_'43''43''45'mono_394 (coe v1)
             (coe MAlonzo.Code.Once.Type.Instance.d_ftvK_6 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v4))
             (coe d_ftvK'8838'ftv_372 (coe v3))
             (coe d_ftvK'8838'ftv_372 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v3 v4
        -> coe
             du_'43''43''45'mono_394 (coe v1)
             (coe MAlonzo.Code.Once.Type.Instance.d_ftvK_6 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v4))
             (coe d_ftvK'8838'ftv_372 (coe v3))
             (coe d_ftvK'8838'ftv_372 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v3
        -> coe d_ftvKF'8838'ftvF_378 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v3 v4
        -> coe d_ftvKF'8838'ftvF_378 (coe v3) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.ftvKF⊆ftvF
d_ftvKF'8838'ftvF_378 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_ftvKF'8838'ftvF_378 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v3 -> coe v2
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v3 v4
        -> coe
             du_'43''43''45'mono_394 (coe v1)
             (coe MAlonzo.Code.Once.Type.Instance.d_ftvKF_8 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftvF_276 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftvF_276 (coe v4))
             (coe d_ftvKF'8838'ftvF_378 (coe v3))
             (coe d_ftvKF'8838'ftvF_378 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v3 v4
        -> coe
             du_'43''43''45'mono_394 (coe v1)
             (coe MAlonzo.Code.Once.Type.Instance.d_ftvKF_8 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftvF_276 (coe v3))
             (coe MAlonzo.Code.Once.Type.Poly.d_ftvF_276 (coe v4))
             (coe d_ftvKF'8838'ftvF_378 (coe v3))
             (coe d_ftvKF'8838'ftvF_378 (coe v4)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.++-mono
d_'43''43''45'mono_394 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'43''43''45'mono_394 v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_'43''43''45'mono_394 v0 v1 v2 v4 v5 v6 v7
du_'43''43''45'mono_394 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'43''43''45'mono_394 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Data.List.Relation.Unary.Any.Properties.du_'43''43''8315'_868
              (coe v1) (coe v6) in
    coe
      (case coe v7 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
           -> coe
                MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                v2 (coe v4 v0 v8)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
           -> coe
                MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                v2 v3 (coe v5 v0 v8)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.Rigid.AllBase
d_AllBase_490 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d_AllBase_490 = erased
-- Once.Type.Rigid.allBase?
d_allBase'63'_508 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_allBase'63'_508 ~v0 v1 v2 v3 = du_allBase'63'_508 v1 v2 v3
du_allBase'63'_508 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_allBase'63'_508 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      (:) v3 v4
        -> let v5
                 = coe
                     MAlonzo.Code.Once.Functor.Decide.du_base'63'_304 (coe v0)
                     (coe v1 v3) in
           coe
             (let v6 = coe du_allBase'63'_508 (coe v0) (coe v1) (coe v4) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                     -> case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                            -> if coe v8
                                 then case coe v9 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                          -> coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                  (coe
                                                     (\ v11 v12 ->
                                                        case coe v12 of
                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v15
                                                            -> coe v7
                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v15
                                                            -> coe v10 v11 v15
                                                          _ -> MAlonzo.RTE.mazUnreachableError)))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v9)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe v8)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                     -> coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                          (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                          (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid._.nothing≢just
d_nothing'8802'just_574 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_574 = erased
-- Once.Type.Rigid.kindedInstance?
d_kindedInstance'63'_586 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_kindedInstance'63'_586 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.Type.Match.d_instantiateAcc_104
              (coe v0) (coe v2) (coe v3)
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> let v6
                    = coe MAlonzo.Code.Once.Type.MatchCorrect.du_θof_522 (coe v5) in
              coe
                (let v7
                       = coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe
                              MAlonzo.Code.Once.Type.MatchCorrect.du_inst'45'sound_854 (coe v0)
                              (coe v2) (coe v3)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v5))
                           v5 erased in
                 coe
                   (let v8
                          = coe
                              du_allBase'63'_508 (coe v1) (coe v6)
                              (coe MAlonzo.Code.Once.Type.Instance.d_ftvK_6 (coe v2)) in
                    coe
                      (case coe v8 of
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                           -> if coe v9
                                then case coe v10 of
                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                         -> coe
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                              (coe v9)
                                              (coe
                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe v7) (coe v11))))
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                else coe
                                       seq (coe v10)
                                       (coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                          (coe v9)
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                         _ -> MAlonzo.RTE.mazUnreachableError)))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.Rigid._.absurd
d_absurd_612 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_absurd_612 = erased
