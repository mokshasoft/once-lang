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

module MAlonzo.Code.Once.Type.Schema where

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
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Instance
import qualified MAlonzo.Code.Once.Type.Poly
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Type.Schema.memberB-sound
d_memberB'45'sound_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_memberB'45'sound_10 v0 v1 ~v2 = du_memberB'45'sound_10 v0 v1
du_memberB'45'sound_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_memberB'45'sound_10 v0 v1
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
                                 (coe du_memberB'45'sound_10 (coe v0) (coe v3)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Schema.memberB-complete
d_memberB'45'complete_46 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_memberB'45'complete_46 = erased
-- Once.Type.Schema.∈-go
d_'8712''45'go_106 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8712''45'go_106 v0 v1 v2 v3
  = case coe v2 of
      (:) v4 v5
        -> let v6
                 = MAlonzo.Code.Once.Type.Instance.d_memberB_44 (coe v4) (coe v1) in
           coe
             (if coe v6
                then case coe v3 of
                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v9
                         -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v9
                         -> coe d_'8712''45'go_106 (coe v0) (coe v1) (coe v5) (coe v9)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else (case coe v3 of
                        MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v9
                          -> coe
                               MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                               (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
                        MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v9
                          -> let v10
                                   = d_'8712''45'go_106
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
-- Once.Type.Schema.∈-params
d_'8712''45'params_220 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'8712''45'params_220 v0 v1 v2
  = let v3
          = d_'8712''45'go_106
              (coe v1) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
              (coe MAlonzo.Code.Once.Type.Poly.d_ftv_274 (coe v0)) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4 -> coe v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.Schema.lookup-∈
d_lookup'45''8712'_250 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_lookup'45''8712'_250 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                    (d_lookup'45''8712'_250 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Schema.positionOf-∈
d_positionOf'45''8712'_268 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_positionOf'45''8712'_268 v0 v1 v2
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
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                       else coe
                              seq (coe v7)
                              (case coe v2 of
                                 MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v10
                                   -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                 MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v10
                                   -> let v11
                                            = d_positionOf'45''8712'_268
                                                (coe v0) (coe v4) (coe v10) in
                                      coe
                                        (case coe v11 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                             -> case coe v13 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Data.Fin.Base.C_suc_16 v12)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            erased (coe v15))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Schema.schemaOf
d_schemaOf_324 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Schema_8
d_schemaOf_324 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Syntax.C_schema_22
      (coe MAlonzo.Code.Once.Type.Instance.d_arityOf_86 (coe v0))
      (coe MAlonzo.Code.Once.Type.Instance.d_kindsOf_166 (coe v0))
      (coe MAlonzo.Code.Once.Type.Instance.d_rigidOf_160 (coe v0))
-- Once.Type.Schema.τOf
d_τOf_332 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_τOf_332 ~v0 v1 v2 v3 = du_τOf_332 v1 v2 v3
du_τOf_332 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_τOf_332 v0 v1 v2
  = coe
      v1
      (coe
         MAlonzo.Code.Data.List.Base.du_lookup_390
         (coe MAlonzo.Code.Once.Type.Instance.d_params_82 (coe v0))
         (coe v2))
-- Once.Type.Schema.τOf-respects
d_τOf'45'respects_348 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Spec.Type.T_Base_84) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_τOf'45'respects_348 ~v0 ~v1 v2 ~v3 v4 v5 ~v6
  = du_τOf'45'respects_348 v2 v4 v5
du_τOf'45'respects_348 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Spec.Type.T_Base_84) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
du_τOf'45'respects_348 v0 v1 v2
  = coe
      v1
      (coe
         MAlonzo.Code.Data.List.Base.du_lookup_390
         (coe MAlonzo.Code.Once.Type.Instance.d_params_82 (coe v0))
         (coe v2))
      (coe
         du_memberB'45'sound_10
         (coe
            MAlonzo.Code.Data.List.Base.du_lookup_390
            (coe MAlonzo.Code.Once.Type.Instance.d_params_82 (coe v0))
            (coe v2))
         (coe MAlonzo.Code.Once.Type.Instance.d_ftvK_6 (coe v0)))
-- Once.Type.Schema._.kb
d_kb_366 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Once.Spec.Type.T_Base_84) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_kb_366 = erased
-- Once.Type.Schema._.var-inst
d_var'45'inst_382 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_var'45'inst_382 = erased
-- Once.Type.Schema._.part-inst
d_part'45'inst_408 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_part'45'inst_408 = erased
-- Once.Type.Schema._.partF-inst
d_partF'45'inst_414 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_partF'45'inst_414 = erased
-- Once.Type.Schema.kinded-instance
d_kinded'45'instance_540 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_kinded'45'instance_540 ~v0 ~v1 v2 ~v3 v4
  = du_kinded'45'instance_540 v2 v4
du_kinded'45'instance_540 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_kinded'45'instance_540 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_τOf_332 (coe v0) (coe v2))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (\ v6 v7 -> coe du_τOf'45'respects_348 (coe v0) (coe v5) v6)
                       erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
