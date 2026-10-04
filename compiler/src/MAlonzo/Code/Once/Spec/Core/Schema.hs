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

module MAlonzo.Code.Once.Spec.Core.Schema where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Spec.Core.AbsTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Spec.Core.Schema.memberB-sound
d_memberB'45'sound_12 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_memberB'45'sound_12 v0 v1 ~v2 = du_memberB'45'sound_12 v0 v1
du_memberB'45'sound_12 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_memberB'45'sound_12 v0 v1
  = case coe v1 of
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v2)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe
                              seq (coe v6)
                              (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
                       else coe
                              seq (coe v6)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                 (coe du_memberB'45'sound_12 (coe v0) (coe v3)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Schema.memberB-complete
d_memberB'45'complete_48 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_memberB'45'complete_48 = erased
-- Once.Spec.Core.Schema.∈-go
d_'8712''45'go_108 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8712''45'go_108 v0 v1 v2 v3
  = case coe v2 of
      (:) v4 v5
        -> let v6
                 = MAlonzo.Code.Once.Type.Rigid.d_memberB_40 (coe v4) (coe v1) in
           coe
             (if coe v6
                then case coe v3 of
                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v9
                         -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v9
                         -> coe d_'8712''45'go_108 (coe v0) (coe v1) (coe v5) (coe v9)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else (case coe v3 of
                        MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v9
                          -> coe
                               MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                               (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
                        MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v9
                          -> let v10
                                   = d_'8712''45'go_108
                                       (coe v0)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                          (coe v1))
                                       (coe v5) (coe v9) in
                             coe
                               (case coe v10 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                                    -> coe
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                            v11)
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                    -> let v12
                                             = coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                 erased
                                                 (\ v12 ->
                                                    coe
                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                      (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                    (coe v0) (coe v4)) in
                                       coe
                                         (case coe v12 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                              -> if coe v13
                                                   then coe
                                                          seq (coe v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                             (coe
                                                                MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                                erased))
                                                   else coe seq (coe v14) (coe v10)
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError)
                        _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Schema.∈-params
d_'8712''45'params_222 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'8712''45'params_222 v0 v1 v2
  = let v3
          = d_'8712''45'go_108
              (coe v1) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
              (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v0)) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Spec.Core.Schema.indexOf-<
d_indexOf'45''60'_252 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_indexOf'45''60'_252 v0 v1 v2
  = case coe v1 of
      (:) v3 v4
        -> let v5
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v5 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v3)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                  -> if coe v6
                       then coe
                              seq (coe v7)
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                 (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
                       else coe
                              seq (coe v7)
                              (case coe v2 of
                                 MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v10
                                   -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                 MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v10
                                   -> coe
                                        MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                        (d_indexOf'45''60'_252 (coe v0) (coe v4) (coe v10))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Schema.lookup-indexOf
d_lookup'45'indexOf_296 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'indexOf_296 = erased
-- Once.Spec.Core.Schema.lookup-∈
d_lookup'45''8712'_338 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_lookup'45''8712'_338 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                    (d_lookup'45''8712'_338 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Schema.kindsOf
d_kindsOf_352 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_TKind_110
d_kindsOf_352 v0 v1
  = coe
      MAlonzo.Code.Once.Type.Rigid.d_kindOf_86 (coe v0)
      (coe
         MAlonzo.Code.Data.List.Base.du_lookup_390
         (coe MAlonzo.Code.Once.Type.Rigid.d_params_78 (coe v0)) (coe v1))
-- Once.Spec.Core.Schema.τOf
d_τOf_360 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108
d_τOf_360 v0 v1 v2
  = coe
      v1
      (coe
         MAlonzo.Code.Data.List.Base.du_lookup_390
         (coe MAlonzo.Code.Once.Type.Rigid.d_params_78 (coe v0)) (coe v2))
-- Once.Spec.Core.Schema.τOf-respects
d_τOf'45'respects_372 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
d_τOf'45'respects_372 v0 ~v1 v2 v3 ~v4
  = du_τOf'45'respects_372 v0 v2 v3
du_τOf'45'respects_372 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196
du_τOf'45'respects_372 v0 v1 v2
  = coe
      v1
      (coe
         MAlonzo.Code.Data.List.Base.du_lookup_390
         (coe MAlonzo.Code.Once.Type.Rigid.d_params_78 (coe v0)) (coe v2))
      (coe
         du_memberB'45'sound_12
         (coe
            MAlonzo.Code.Data.List.Base.du_lookup_390
            (coe MAlonzo.Code.Once.Type.Rigid.d_params_78 (coe v0)) (coe v2))
         (coe MAlonzo.Code.Once.Type.Rigid.d_ftvK_6 (coe v0)))
-- Once.Spec.Core.Schema._.kb
d_kb_390 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_kb_390 = erased
-- Once.Spec.Core.Schema.schemaOf
d_schemaOf_394 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Schema_846
d_schemaOf_394 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTy.C_schema_860
      (coe MAlonzo.Code.Once.Type.Rigid.d_arityOf_82 (coe v0))
      (coe d_kindsOf_352 (coe v0))
      (coe
         MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82
         (coe MAlonzo.Code.Once.Type.Rigid.d_arityOf_82 (coe v0))
         (coe d_kindsOf_352 (coe v0))
         (coe MAlonzo.Code.Once.Type.Rigid.d_rigidOf_124 (coe v0)))
-- Once.Spec.Core.Schema.Var.ps
d_ps_406 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_ps_406 v0 ~v1 ~v2 = du_ps_406 v0
du_ps_406 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_ps_406 v0
  = coe MAlonzo.Code.Once.Type.Rigid.d_params_78 (coe v0)
-- Once.Spec.Core.Schema.Var.mp
d_mp_408 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_mp_408 v0 v1 v2
  = coe d_'8712''45'params_222 (coe v0) (coe v1) (coe v2)
-- Once.Spec.Core.Schema.Var.j
d_j_410 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_j_410 v0 v1 ~v2 = du_j_410 v0 v1
du_j_410 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_j_410 v0 v1
  = coe
      MAlonzo.Code.Data.Fin.Base.du_fromℕ'60'_52
      (coe
         MAlonzo.Code.Once.Type.Rigid.d_indexOf_92 (coe v1)
         (coe
            MAlonzo.Code.Once.Type.Rigid.d_nubFrom_66
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe MAlonzo.Code.Once.Type.d_ftv_632 (coe v0))))
-- Once.Spec.Core.Schema.Var.kind-at
d_kind'45'at_412 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_kind'45'at_412 = erased
-- Once.Spec.Core.Schema.Var.abstracts
d_abstracts_414 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_abstracts_414 = erased
-- Once.Spec.Core.Schema.Var._.k
d_k_420 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Once.Type.T_TKind_110
d_k_420 v0 v1 ~v2 = du_k_420 v0 v1
du_k_420 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_TKind_110
du_k_420 v0 v1
  = coe MAlonzo.Code.Once.Type.Rigid.d_kindOf_86 (coe v0) (coe v1)
-- Once.Spec.Core.Schema.Var._.i
d_i_422 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> Integer
d_i_422 v0 v1 ~v2 = du_i_422 v0 v1
du_i_422 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
du_i_422 v0 v1
  = coe
      MAlonzo.Code.Once.Type.Rigid.d_indexOf_92 (coe v1)
      (coe du_ps_406 (coe v0))
-- Once.Spec.Core.Schema.Var._.kd
d_kd_428 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_kd_428 = erased
-- Once.Spec.Core.Schema.Var._.go
d_go_438 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_438 = erased
-- Once.Spec.Core.Schema.Var.lookup-at
d_lookup'45'at_444 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'at_444 = erased
-- Once.Spec.Core.Schema.part-cf
d_part'45'cf_452 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374
d_part'45'cf_452 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_PUnit_264
        -> coe MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'Unit_386
      MAlonzo.Code.Once.Type.C_PVoid_266
        -> coe MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'Void_388
      MAlonzo.Code.Once.Type.C__P'42'__268 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45''42'_398
             (d_part'45'cf_452
                (coe v0) (coe v3)
                (coe
                   (\ v5 v6 ->
                      coe
                        v2 v5
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v3)) v6))))
             (d_part'45'cf_452
                (coe v0) (coe v4)
                (coe
                   (\ v5 v6 ->
                      coe
                        v2 v5
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v3))
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v4)) v6))))
      MAlonzo.Code.Once.Type.C__P'43'__270 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45''43'_404
             (d_part'45'cf_452
                (coe v0) (coe v3)
                (coe
                   (\ v5 v6 ->
                      coe
                        v2 v5
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v3)) v6))))
             (d_part'45'cf_452
                (coe v0) (coe v4)
                (coe
                   (\ v5 v6 ->
                      coe
                        v2 v5
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v3))
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v4)) v6))))
      MAlonzo.Code.Once.Type.C__P'8658''91'_'93'__272 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45''8658'_412
             (d_part'45'cf_452
                (coe v0) (coe v3)
                (coe
                   (\ v6 v7 ->
                      coe
                        v2 v6
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v3)) v7))))
             (d_part'45'cf_452
                (coe v0) (coe v5)
                (coe
                   (\ v6 v7 ->
                      coe
                        v2 v6
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v3))
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v5)) v7))))
      MAlonzo.Code.Once.Type.C_PEff_274 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45''8658'_412
             (d_part'45'cf_452
                (coe v0) (coe v3)
                (coe
                   (\ v5 v6 ->
                      coe
                        v2 v5
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v3)) v6))))
             (d_part'45'cf_452
                (coe v0) (coe v4)
                (coe
                   (\ v5 v6 ->
                      coe
                        v2 v5
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v3))
                           (MAlonzo.Code.Once.Type.d_ftv_632 (coe v4)) v6))))
      MAlonzo.Code.Once.Type.C_Pμ'45'type_276 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'μ_416
             (d_partF'45'cf_460 (coe v0) (coe v3) (coe v2))
      MAlonzo.Code.Once.Type.C_Pν'45'type_278 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'ν_422
             (d_partF'45'cf_460 (coe v0) (coe v3) (coe v2))
      MAlonzo.Code.Once.Type.C_PInt_280
        -> coe MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'Int_390
      MAlonzo.Code.Once.Type.C_PFloat_282
        -> coe MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'Float_392
      MAlonzo.Code.Once.Type.C_PTVar_284 v3
        -> coe MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'var_384
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Schema.partF-cf
d_partF'45'cf_460 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFreeF_378
d_partF'45'cf_460 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_PK_256 v3
        -> coe
             MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'K_428
             (d_part'45'cf_452 (coe v0) (coe v3) (coe v2))
      MAlonzo.Code.Once.Type.C_PId_258
        -> coe MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45'Id_430
      MAlonzo.Code.Once.Type.C__P'8853'__260 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45''8853'_436
             (d_partF'45'cf_460
                (coe v0) (coe v3)
                (coe
                   (\ v5 v6 ->
                      coe
                        v2 v5
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                           (MAlonzo.Code.Once.Type.d_ftvF_634 (coe v3)) v6))))
             (d_partF'45'cf_460
                (coe v0) (coe v4)
                (coe
                   (\ v5 v6 ->
                      coe
                        v2 v5
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                           (MAlonzo.Code.Once.Type.d_ftvF_634 (coe v3))
                           (MAlonzo.Code.Once.Type.d_ftvF_634 (coe v4)) v6))))
      MAlonzo.Code.Once.Type.C__P'8855'__262 v3 v4
        -> coe
             MAlonzo.Code.Once.Spec.Core.AbsTy.C_cf'45''8855'_442
             (d_partF'45'cf_460
                (coe v0) (coe v3)
                (coe
                   (\ v5 v6 ->
                      coe
                        v2 v5
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''737'_194
                           (MAlonzo.Code.Once.Type.d_ftvF_634 (coe v3)) v6))))
             (d_partF'45'cf_460
                (coe v0) (coe v4)
                (coe
                   (\ v5 v6 ->
                      coe
                        v2 v5
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45''43''43''8314''691'_200
                           (MAlonzo.Code.Once.Type.d_ftvF_634 (coe v3))
                           (MAlonzo.Code.Once.Type.d_ftvF_634 (coe v4)) v6))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Schema.part-inst
d_part'45'inst_590 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_part'45'inst_590 = erased
-- Once.Spec.Core.Schema.partF-inst
d_partF'45'inst_600 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyFunctor_252 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_partF'45'inst_600 = erased
-- Once.Spec.Core.Schema.schemaOf-cf
d_schemaOf'45'cf_766 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374
d_schemaOf'45'cf_766 v0
  = coe d_part'45'cf_452 (coe v0) (coe v0) (coe (\ v1 v2 -> v2))
-- Once.Spec.Core.Schema.kinded-instance
d_kinded'45'instance_778 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_kinded'45'instance_778 v0 ~v1 v2
  = du_kinded'45'instance_778 v0 v2
du_kinded'45'instance_778 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_kinded'45'instance_778 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_τOf_360 (coe v0) (coe v2))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (\ v6 v7 -> coe du_τOf'45'respects_372 (coe v0) (coe v5) v6)
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
