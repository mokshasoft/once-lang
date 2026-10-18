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
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Instance
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Type.Instance
import qualified MAlonzo.Code.Once.Type.Match
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Type.Rigid.subst-ground
d_subst'45'ground_12 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'ground_12 = erased
-- Once.Type.Rigid.subst-groundF
d_subst'45'groundF_20 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'groundF_20 = erased
-- Once.Type.Rigid.++-⊥
d_'43''43''45''8869'_146 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''43''45''8869'_146 = erased
-- Once.Type.Rigid.ftv-ground
d_ftv'45'ground_190 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftv'45'ground_190 = erased
-- Once.Type.Rigid.ftvF-ground
d_ftvF'45'ground_196 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftvF'45'ground_196 = erased
-- Once.Type.Rigid.ftvK-ground
d_ftvK'45'ground_270 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftvK'45'ground_270 = erased
-- Once.Type.Rigid.ftvKF-ground
d_ftvKF'45'ground_276 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ftvKF'45'ground_276 = erased
-- Once.Type.Rigid.ground-kinded
d_ground'45'kinded_350 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground'45'kinded_350 ~v0 ~v1 = du_ground'45'kinded_350
du_ground'45'kinded_350 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ground'45'kinded_350
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 -> coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            (\ v0 v1 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
-- Once.Type.Rigid.ftvK⊆ftv
d_ftvK'8838'ftv_364 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_ftvK'8838'ftv_364 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v3 v4
        -> coe
             du_'43''43''45'mono_386 (coe v1)
             (coe MAlonzo.Code.Once.Lang.Type.Instance.d_ftvK_8 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v4))
             (coe d_ftvK'8838'ftv_364 (coe v3))
             (coe d_ftvK'8838'ftv_364 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v3 v4
        -> coe
             du_'43''43''45'mono_386 (coe v1)
             (coe MAlonzo.Code.Once.Lang.Type.Instance.d_ftvK_8 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v4))
             (coe d_ftvK'8838'ftv_364 (coe v3))
             (coe d_ftvK'8838'ftv_364 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v3 v4 v5
        -> coe
             du_'43''43''45'mono_386 (coe v1)
             (coe MAlonzo.Code.Once.Lang.Type.Instance.d_ftvK_8 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v5))
             (coe d_ftvK'8838'ftv_364 (coe v3))
             (coe d_ftvK'8838'ftv_364 (coe v5)) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v3 v4
        -> coe
             du_'43''43''45'mono_386 (coe v1)
             (coe MAlonzo.Code.Once.Lang.Type.Instance.d_ftvK_8 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v4))
             (coe d_ftvK'8838'ftv_364 (coe v3))
             (coe d_ftvK'8838'ftv_364 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v3 v4
        -> coe
             du_'43''43''45'mono_386 (coe v1)
             (coe MAlonzo.Code.Once.Lang.Type.Instance.d_ftvK_8 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftv_246 (coe v4))
             (coe d_ftvK'8838'ftv_364 (coe v3))
             (coe d_ftvK'8838'ftv_364 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v3
        -> coe d_ftvKF'8838'ftvF_370 (coe v3) (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v3 v4
        -> coe d_ftvKF'8838'ftvF_370 (coe v3) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.ftvKF⊆ftvF
d_ftvKF'8838'ftvF_370 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_ftvKF'8838'ftvF_370 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v3 -> coe v2
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v3 v4
        -> coe
             du_'43''43''45'mono_386 (coe v1)
             (coe MAlonzo.Code.Once.Lang.Type.Instance.d_ftvKF_10 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftvF_248 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftvF_248 (coe v4))
             (coe d_ftvKF'8838'ftvF_370 (coe v3))
             (coe d_ftvKF'8838'ftvF_370 (coe v4)) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v3 v4
        -> coe
             du_'43''43''45'mono_386 (coe v1)
             (coe MAlonzo.Code.Once.Lang.Type.Instance.d_ftvKF_10 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftvF_248 (coe v3))
             (coe MAlonzo.Code.Once.Lang.Type.Poly.d_ftvF_248 (coe v4))
             (coe d_ftvKF'8838'ftvF_370 (coe v3))
             (coe d_ftvKF'8838'ftvF_370 (coe v4)) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.++-mono
d_'43''43''45'mono_386 ::
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
d_'43''43''45'mono_386 v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_'43''43''45'mono_386 v0 v1 v2 v4 v5 v6 v7
du_'43''43''45'mono_386 ::
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
du_'43''43''45'mono_386 v0 v1 v2 v3 v4 v5 v6
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
d_AllBase_480 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d_AllBase_480 = erased
-- Once.Type.Rigid.allBase?
d_allBase'63'_492 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_allBase'63'_492 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      (:) v2 v3
        -> let v4
                 = MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                     (coe v0 v2) in
           coe
             (let v5 = d_allBase'63'_492 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                          -> coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe v7)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                  (coe
                                                     (\ v10 v11 ->
                                                        case coe v11 of
                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v14
                                                            -> coe v6
                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v14
                                                            -> coe v9 v10 v14
                                                          _ -> MAlonzo.RTE.mazUnreachableError)))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 else coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe v7)
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
d_nothing'8802'just_548 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_548 = erased
-- Once.Type.Rigid.kindedInstance?
d_kindedInstance'63'_556 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_kindedInstance'63'_556 v0 v1
  = let v2
          = MAlonzo.Code.Once.Type.Match.d_instantiateAcc_92
              (coe v0) (coe v1)
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> let v4 = MAlonzo.Code.Once.Type.Instance.d_θof_492 (coe v3) in
              coe
                (let v5
                       = coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                           (coe
                              MAlonzo.Code.Once.Type.Instance.du_inst'45'sound_812 (coe v0)
                              (coe v1) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                              (coe v3))
                           v3 erased in
                 coe
                   (let v6
                          = d_allBase'63'_492
                              (coe v4)
                              (coe MAlonzo.Code.Once.Lang.Type.Instance.d_ftvK_8 (coe v0)) in
                    coe
                      (case coe v6 of
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                           -> if coe v7
                                then case coe v8 of
                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                         -> coe
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                              (coe v7)
                                              (coe
                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe v5) (coe v9))))
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                else coe
                                       seq (coe v8)
                                       (coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                          (coe v7)
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
d_absurd_578 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_absurd_578 = erased
-- Once.Type.Rigid.both
d_both_652 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d_both_652 ~v0 ~v1 ~v2 v3 v4 v5 = du_both_652 v3 v4 v5
du_both_652 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
du_both_652 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v4 v5)
                _ -> coe v3
         _ -> coe v3)
-- Once.Type.Rigid.one
d_one_666 ::
  () -> () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_one_666 ~v0 ~v1 v2 v3 = du_one_666 v2 v3
du_one_666 ::
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_one_666 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.rigidFree?
d_rigidFree'63'_676 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
d_rigidFree'63'_676 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Unit_72)
      MAlonzo.Code.Once.Lang.Type.C_Void_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Void_74)
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             du_both_652
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''42'_84)
             (coe d_rigidFree'63'_676 (coe v1))
             (coe d_rigidFree'63'_676 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             du_both_652
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''43'_90)
             (coe d_rigidFree'63'_676 (coe v1))
             (coe d_rigidFree'63'_676 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe
             du_both_652
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8658'_98)
             (coe d_rigidFree'63'_676 (coe v1))
             (coe d_rigidFree'63'_676 (coe v3))
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe
             du_one_666
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'μ_102)
             (coe d_rigidFreeF'63'_680 (coe v1))
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe
             du_one_666
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'ν_108)
             (coe d_rigidFreeF'63'_680 (coe v1))
      MAlonzo.Code.Once.Lang.Type.C_Int_34
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Int_76)
      MAlonzo.Code.Once.Lang.Type.C_Float_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Float_78)
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.rigidFreeF?
d_rigidFreeF'63'_680 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  Maybe MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFreeF_70
d_rigidFreeF'63'_680 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v1
        -> coe
             du_one_666
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'K_112)
             (coe d_rigidFree'63'_676 (coe v1))
      MAlonzo.Code.Once.Lang.Type.C_Id_14
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Id_114)
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v1 v2
        -> coe
             du_both_652
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8853'_120)
             (coe d_rigidFreeF'63'_680 (coe v1))
             (coe d_rigidFreeF'63'_680 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v1 v2
        -> coe
             du_both_652
             (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8855'_126)
             (coe d_rigidFreeF'63'_680 (coe v1))
             (coe d_rigidFreeF'63'_680 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.rigidFree?-complete
d_rigidFree'63''45'complete_716 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rigidFree'63''45'complete_716 = erased
-- Once.Type.Rigid.rigidFreeF?-complete
d_rigidFreeF'63''45'complete_722 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFreeF_70 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rigidFreeF'63''45'complete_722 = erased
-- Once.Type.Rigid.extractGround-rf
d_extractGround'45'rf_806 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFree_68
d_extractGround'45'rf_806 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20
        -> coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Unit_72
      MAlonzo.Code.Once.Lang.Type.Poly.C_PVoid_22
        -> coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Void_74
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''42'_84
                    (d_extractGround'45'rf_806 (coe v2) (coe v4))
                    (d_extractGround'45'rf_806 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''43'_90
                    (d_extractGround'45'rf_806 (coe v2) (coe v4))
                    (d_extractGround'45'rf_806 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8658'_98
                    (d_extractGround'45'rf_806 (coe v2) (coe v5))
                    (d_extractGround'45'rf_806 (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8658'_98
                    (d_extractGround'45'rf_806 (coe v2) (coe v4))
                    (d_extractGround'45'rf_806 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8658'_98
                    (d_extractGround'45'rf_806 (coe v2) (coe v4))
                    (d_extractGround'45'rf_806 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v2
        -> coe
             MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'μ_102
             (d_extractGroundF'45'rf_812 (coe v2) (coe v1))
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v2 v3
        -> coe
             MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'ν_108
             (d_extractGroundF'45'rf_812 (coe v2) (coe v1))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38
        -> coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Int_76
      MAlonzo.Code.Once.Lang.Type.Poly.C_PFloat_40
        -> coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Float_78
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Rigid.extractGroundF-rf
d_extractGroundF'45'rf_812 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Type.WellFormed.T_RigidFreeF_70
d_extractGroundF'45'rf_812 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v2
        -> coe
             MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'K_112
             (d_extractGround'45'rf_806 (coe v2) (coe v1))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14
        -> coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45'Id_114
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8853'_120
                    (d_extractGroundF'45'rf_812 (coe v2) (coe v4))
                    (d_extractGroundF'45'rf_812 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Type.WellFormed.C_rf'45''8855'_126
                    (d_extractGroundF'45'rf_812 (coe v2) (coe v4))
                    (d_extractGroundF'45'rf_812 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
