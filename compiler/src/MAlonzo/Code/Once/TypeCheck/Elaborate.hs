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

module MAlonzo.Code.Once.TypeCheck.Elaborate where

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
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Surface.Thinning
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Elaborate.≟F-K-aux
d_'8799'F'45'K'45'aux_10 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'F'45'K'45'aux_10 ~v0 ~v1 v2 = du_'8799'F'45'K'45'aux_10 v2
du_'8799'F'45'K'45'aux_10 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'F'45'K'45'aux_10 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
             else coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.≟F-⊕-aux
d_'8799'F'45''8853''45'aux_24 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'F'45''8853''45'aux_24 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'F'45''8853''45'aux_24 v4 v5
du_'8799'F'45''8853''45'aux_24 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'F'45''8853''45'aux_24 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.≟F-⊗-aux
d_'8799'F'45''8855''45'aux_46 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'F'45''8855''45'aux_46 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'F'45''8855''45'aux_46 v4 v5
du_'8799'F'45''8855''45'aux_46 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'F'45''8855''45'aux_46 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.≟T-*-aux
d_'8799'T'45''42''45'aux_68 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'T'45''42''45'aux_68 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'T'45''42''45'aux_68 v4 v5
du_'8799'T'45''42''45'aux_68 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'T'45''42''45'aux_68 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.≟T-+-aux
d_'8799'T'45''43''45'aux_90 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'T'45''43''45'aux_90 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8799'T'45''43''45'aux_90 v4 v5
du_'8799'T'45''43''45'aux_90 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'T'45''43''45'aux_90 v0 v1
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> if coe v4
                              then coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v4)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                         -> coe
                              seq (coe v4)
                              (coe
                                 seq (coe v5)
                                 (coe
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                    (coe v2)
                                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.≟T-⇒-aux
d_'8799'T'45''8658''45'aux_116 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'T'45''8658''45'aux_116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'8799'T'45''8658''45'aux_116 v6 v7 v8
du_'8799'T'45''8658''45'aux_116 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'T'45''8658''45'aux_116 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (case coe v2 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                          -> if coe v7
                                               then coe
                                                      seq (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v7)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                            erased))
                                               else coe
                                                      seq (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v7)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe
                                     seq (coe v6)
                                     (case coe v2 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                          -> coe
                                               seq (coe v7)
                                               (coe
                                                  seq (coe v8)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v5)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v4)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> coe
                              seq (coe v5)
                              (coe
                                 seq (coe v6)
                                 (case coe v2 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                      -> coe
                                           seq (coe v7)
                                           (coe
                                              seq (coe v8)
                                              (coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                 (coe v3)
                                                 (coe
                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.≟T-μ-aux
d_'8799'T'45'μ'45'aux_150 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'T'45'μ'45'aux_150 ~v0 ~v1 v2
  = du_'8799'T'45'μ'45'aux_150 v2
du_'8799'T'45'μ'45'aux_150 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'T'45'μ'45'aux_150 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
             else coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.≟T-ν-aux
d_'8799'T'45'ν'45'aux_160 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'T'45'ν'45'aux_160 ~v0 ~v1 v2
  = du_'8799'T'45'ν'45'aux_160 v2
du_'8799'T'45'ν'45'aux_160 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'T'45'ν'45'aux_160 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
             else coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v1)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._≟F_
d__'8799'F__170 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__170 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_110 v3
               -> coe
                    du_'8799'F'45'K'45'aux_10 (coe d__'8799'T__176 (coe v2) (coe v3))
             MAlonzo.Code.Once.Type.C_Id_112
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__114 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__116 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Id_112
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_110 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_112
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'8853'__114 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__116 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8853'__114 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_110 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_112
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__114 v4 v5
               -> coe
                    du_'8799'F'45''8853''45'aux_24
                    (coe d__'8799'F__170 (coe v2) (coe v4))
                    (coe d__'8799'F__170 (coe v3) (coe v5))
             MAlonzo.Code.Once.Type.C__'8855'__116 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_110 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Id_112
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8853'__114 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8855'__116 v4 v5
               -> coe
                    du_'8799'F'45''8855''45'aux_46
                    (coe d__'8799'F__170 (coe v2) (coe v4))
                    (coe d__'8799'F__170 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._≟T_
d__'8799'T__176 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'T__176 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Void_120
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v4 v5
               -> coe
                    du_'8799'T'45''42''45'aux_68
                    (coe d__'8799'T__176 (coe v2) (coe v4))
                    (coe d__'8799'T__176 (coe v3) (coe v5))
             MAlonzo.Code.Once.Type.C__'43'__124 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v4 v5
               -> coe
                    du_'8799'T'45''43''45'aux_90
                    (coe d__'8799'T__176 (coe v2) (coe v4))
                    (coe d__'8799'T__176 (coe v3) (coe v5))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v5 v6 v7
               -> coe
                    du_'8799'T'45''8658''45'aux_116
                    (coe d__'8799'T__176 (coe v2) (coe v5))
                    (coe MAlonzo.Code.Once.Type.d__'8799'k__96 (coe v3) (coe v6))
                    (coe d__'8799'T__176 (coe v4) (coe v7))
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
               -> coe
                    du_'8799'T'45'μ'45'aux_150 (coe d__'8799'F__170 (coe v2) (coe v3))
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v3
               -> coe
                    du_'8799'T'45'ν'45'aux_160 (coe d__'8799'F__170 (coe v2) (coe v3))
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_132
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Float_134
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Str_136
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.InferElabResult
d_InferElabResult_238 a0 a1 = ()
data T_InferElabResult_238
  = C_success_252 MAlonzo.Code.Once.Type.T_Type_108
                  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_failure_254 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.CheckElabResult
d_CheckElabResult_262 a0 a1 a2 = ()
data T_CheckElabResult_262
  = C_success_276 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_failure_278 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.Imports
d_Imports_280 :: ()
d_Imports_280 = erased
-- Once.TypeCheck.Elaborate.emptyImports
d_emptyImports_282 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyImports_282
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Elaborate.PolyCtx
d_PolyCtx_284 :: ()
d_PolyCtx_284 = erased
-- Once.TypeCheck.Elaborate.emptyPolyCtx
d_emptyPolyCtx_286 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyPolyCtx_286
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Elaborate.lookupPoly
d_lookupPoly_288 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPoly_288 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe v1)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe
                                        seq (coe v8)
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                                 else coe seq (coe v8) (coe d_lookupPoly_288 (coe v3) (coe v1))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.removePoly
d_removePoly_324 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_removePoly_324 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe v0)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe seq (coe v8) (coe v3)
                                 else coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                                           (coe d_removePoly_324 (coe v0) (coe v3)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.removePoly-decreases
d_removePoly'45'decreases_366 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_removePoly'45'decreases_366 ~v0 v1 v2 ~v3
  = du_removePoly'45'decreases_366 v1 v2
du_removePoly'45'decreases_366 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_removePoly'45'decreases_366 v0 v1
  = case coe v1 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe v0)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                 (coe
                                                    (\ v9 v10 ->
                                                       addInt (coe (1 :: Integer)) (coe v10)))
                                                 (coe (0 :: Integer)) (coe v3))))
                                 else coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                           (coe du_removePoly'45'decreases_366 (coe v0) (coe v3)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx
d_NamedCtx_410 = ()
data T_NamedCtx_410
  = C_mkCtx_436 Integer
                [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
                MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 Integer
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.TypeCheck.Elaborate.NamedCtx.size
d_size_424 :: T_NamedCtx_410 -> Integer
d_size_424 v0
  = case coe v0 of
      C_mkCtx_436 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.named
d_named_426 ::
  T_NamedCtx_410 -> [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_named_426 v0
  = case coe v0 of
      C_mkCtx_436 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.debruijn
d_debruijn_428 ::
  T_NamedCtx_410 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_debruijn_428 v0
  = case coe v0 of
      C_mkCtx_436 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.freshCounter
d_freshCounter_430 :: T_NamedCtx_410 -> Integer
d_freshCounter_430 v0
  = case coe v0 of
      C_mkCtx_436 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.imports
d_imports_432 ::
  T_NamedCtx_410 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports_432 v0
  = case coe v0 of
      C_mkCtx_436 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.NamedCtx.polys
d_polys_434 ::
  T_NamedCtx_410 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polys_434 v0
  = case coe v0 of
      C_mkCtx_436 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.emptyCtx
d_emptyCtx_438 :: T_NamedCtx_410
d_emptyCtx_438
  = coe
      C_mkCtx_436 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe d_emptyImports_282)
      (coe d_emptyPolyCtx_286)
-- Once.TypeCheck.Elaborate.ctxWithImports
d_ctxWithImports_440 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_410
d_ctxWithImports_440 v0
  = coe
      C_mkCtx_436 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe d_emptyPolyCtx_286)
-- Once.TypeCheck.Elaborate.ctxWithImportsAndPolys
d_ctxWithImportsAndPolys_444 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_410
d_ctxWithImportsAndPolys_444 v0 v1
  = coe
      C_mkCtx_436 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe v1)
-- Once.TypeCheck.Elaborate.ctxWithImportsAndSelf
d_ctxWithImportsAndSelf_450 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_NamedCtx_410
d_ctxWithImportsAndSelf_450 v0 v1 v2
  = coe
      d_ctxWithImports_440
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
         (coe v0))
-- Once.TypeCheck.Elaborate.ctxWithImportsAndSelfAndPolys
d_ctxWithImportsAndSelfAndPolys_458 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_NamedCtx_410
d_ctxWithImportsAndSelfAndPolys_458 v0 v1 v2 v3
  = coe
      d_ctxWithImportsAndPolys_444
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
         (coe v0))
      (coe v1)
-- Once.TypeCheck.Elaborate.extendNamedCtx
d_extendNamedCtx_468 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_NamedCtx_410
d_extendNamedCtx_468 v0 v1 v2
  = case coe v0 of
      C_mkCtx_436 v3 v4 v5 v6 v7 v8
        -> coe
             C_mkCtx_436 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v5) (coe v2))
             (coe v6) (coe v7) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.bumpFresh
d_bumpFresh_486 :: T_NamedCtx_410 -> T_NamedCtx_410
d_bumpFresh_486 v0
  = case coe v0 of
      C_mkCtx_436 v1 v2 v3 v4 v5 v6
        -> coe
             C_mkCtx_436 (coe v1) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.freshTVar
d_freshTVar_500 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_freshTVar_500 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("\945" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Elaborate.specId
d_specId_506 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specId_506 ~v0 = du_specId_506
du_specId_506 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specId_506
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_var_182
         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
-- Once.TypeCheck.Elaborate.specFst
d_specFst_514 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specFst_514 ~v0 v1 = du_specFst_514 v1
du_specFst_514 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specFst_514 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v0
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specSnd
d_specSnd_524 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specSnd_524 v0 ~v1 = du_specSnd_524 v0
du_specSnd_524 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specSnd_524 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v0
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specInl
d_specInl_534 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specInl_534 ~v0 ~v1 = du_specInl_534
du_specInl_534 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specInl_534
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_inl''_278
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specInr
d_specInr_544 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specInr_544 ~v0 ~v1 = du_specInr_544
du_specInr_544 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specInr_544
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_inr''_290
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specUnitGen
d_specUnitGen_550 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specUnitGen_550 = coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318
-- Once.TypeCheck.Elaborate.specPair
d_specPair_558 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specPair_558 v0 ~v1 ~v2 = du_specPair_558 v0
du_specPair_558 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specPair_558 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe
            MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_Zero_6)))
         (coe
            MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_Zero_6))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_198
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)))
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_One_8)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_198
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8)))
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_pair_242
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specTerminal
d_specTerminal_568 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specTerminal_568 ~v0 = du_specTerminal_568
du_specTerminal_568 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specTerminal_568
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_Zero_6)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
-- Once.TypeCheck.Elaborate.specInitial
d_specInitial_574 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specInitial_574 ~v0 = du_specInitial_574
du_specInitial_574 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specInitial_574
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_absurd_328
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.specCurry
d_specCurry_584 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specCurry_584 v0 v1 ~v2 = du_specCurry_584 v0 v1
du_specCurry_584 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specCurry_584 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe MAlonzo.Code.Once.Type.C_Zero_6))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_198
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_198
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe MAlonzo.Code.Once.Type.C_One_8))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_app_214
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe MAlonzo.Code.Once.Type.C_One_8))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6))
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6))
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_182
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_pair_242
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specApply
d_specApply_596 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specApply_596 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Type.C_One_8)))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_app_214
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))
         v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v0
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_182
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_snd''_266
            (MAlonzo.Code.Once.Type.d__'8658'__146 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_182
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.TypeCheck.Elaborate.specCompose
d_specCompose_608 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specCompose_608 v0 v1 ~v2 = du_specCompose_608 v0 v1
du_specCompose_608 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specCompose_608 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe
               MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_198
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_198
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_app_214
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
               v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_182
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_182
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specArr
d_specArr_620 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_specArr_620 ~v0 ~v1 = du_specArr_620
du_specArr_620 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_specArr_620
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_arr''_486
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_var_182
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
-- Once.TypeCheck.Elaborate.lookupImport
d_lookupImport_626 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_lookupImport_626 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v4))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                               (coe v1)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_lookupImport_626 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine
d_AppSpine_656 = ()
data T_AppSpine_656
  = C_mkSpine_666 MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
-- Once.TypeCheck.Elaborate.AppSpine.head
d_head_662 ::
  T_AppSpine_656 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_head_662 v0
  = case coe v0 of
      C_mkSpine_666 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine.args
d_args_664 ::
  T_AppSpine_656 -> [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
d_args_664 v0
  = case coe v0 of
      C_mkSpine_666 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.spineOf
d_spineOf_668 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppSpine_656
d_spineOf_668 v0
  = coe
      du_go_676 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Elaborate._.go
d_go_676 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_656
d_go_676 ~v0 v1 v2 = du_go_676 v1 v2
du_go_676 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_656
du_go_676 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> coe C_mkSpine_666 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> coe C_mkSpine_666 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v2 v3
        -> coe
             du_go_676 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v2 v3
        -> coe C_mkSpine_666 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v2 v3 v4
        -> coe C_mkSpine_666 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v2 v3
        -> coe C_mkSpine_666 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v2 v3 v4 v5 v6
        -> coe C_mkSpine_666 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe C_mkSpine_666 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v2
        -> coe C_mkSpine_666 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v2
        -> coe C_mkSpine_666 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v2 v3
        -> coe C_mkSpine_666 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v2 v3 v4
        -> coe C_mkSpine_666 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v3
        -> coe
             C_mkSpine_666
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v3) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isPolyBuiltin
d_isPolyBuiltin_756 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isPolyBuiltin_756 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         l | (==) l ("apply" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("arr" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("compose" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("curry" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("fst" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("id" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("initial" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("inl" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("inr" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("pair" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("snd" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("terminal" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         l | (==) l ("unit" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.lookupLocal
d_lookupLocal_764 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal_764 v0 v1
  = case coe v0 of
      C_mkCtx_436 v2 v3 v4 v5 v6 v7
        -> coe du_go_786 (coe v1) (coe v2) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_786 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_go_786 v6 v7 v8 v9
du_go_786 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_786 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v7 v8 v9
               -> let v10 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (let v11
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v0))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_name_14 (coe v4))) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                            -> if coe v12
                                 then coe
                                        seq (coe v13)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Syntax.d_singleUse_66
                                                    (coe v1)
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                    (coe MAlonzo.Code.Once.Type.C_One_8))
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Syntax.C_var_182
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                 else coe
                                        seq (coe v13)
                                        (let v14
                                               = coe
                                                   du_go_786 (coe v0) (coe v10) (coe v5) (coe v7) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                -> case coe v15 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                       -> case coe v17 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v16)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_Zero_6)
                                                                            v18)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Thinning.du_weaken_910
                                                                            (coe v7) (coe v8)
                                                                            (coe v16) (coe v9)
                                                                            (coe v19))))
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe v14
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.findLocalVarUsage
d_findLocalVarUsage_854 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findLocalVarUsage_854 v0 v1
  = case coe v0 of
      C_mkCtx_436 v2 v3 v4 v5 v6 v7
        -> coe du_go_870 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.go
d_go_870 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_870 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 = du_go_870 v6 v8 v9
du_go_870 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_870 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v6 v7 v8
               -> let v9
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v9 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v0))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                               (coe MAlonzo.Code.Once.TypeCheck.Context.d_name_14 (coe v3))) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                         -> if coe v10
                              then coe
                                     seq (coe v11)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v8)))
                              else coe
                                     seq (coe v11)
                                     (let v12 = coe du_go_870 (coe v0) (coe v4) (coe v6) in
                                      coe
                                        (case coe v12 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                             -> case coe v13 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                               v14)
                                                            (coe v15))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v12
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.matchInferResult
d_matchInferResult_940 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_InferElabResult_238 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_262
d_matchInferResult_940 ~v0 ~v1 v2 v3
  = du_matchInferResult_940 v2 v3
du_matchInferResult_940 ::
  T_InferElabResult_238 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_262
du_matchInferResult_940 v0 v1
  = case coe v0 of
      C_success_252 v2 v3 v4 v5 v6
        -> let v7 = d__'8799'T__176 (coe v1) (coe v2) in
           coe
             (case coe v7 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                  -> if coe v8
                       then coe
                              seq (coe v9)
                              (coe C_success_276 (coe v3) (coe v4) (coe v5) (coe v6))
                       else coe
                              seq (coe v9)
                              (coe
                                 C_failure_278
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v1)
                                    (coe v2)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_254 v2 -> coe C_failure_278 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.FunProjection
d_FunProjection_988 a0 a1 = ()
data T_FunProjection_988
  = C_isFun_1002 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Type.T_Quantity_4
                 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_isEff_1010 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_notFun_1012 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asFun
d_asFun_1018 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_InferElabResult_238 -> T_FunProjection_988
d_asFun_1018 ~v0 ~v1 v2 = du_asFun_1018 v2
du_asFun_1018 :: T_InferElabResult_238 -> T_FunProjection_988
du_asFun_1018 v0
  = case coe v0 of
      C_success_252 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    C_notFun_1012
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    C_notFun_1012
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> coe
                    C_notFun_1012
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    C_notFun_1012
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Once.Type.C_pure_34
                             -> coe
                                  C_isFun_1002 (coe v6) (coe v9) (coe v8) (coe v2) (coe v3) (coe v4)
                                  (coe v5)
                           MAlonzo.Code.Once.Type.C_eff_36
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         C_notFun_1012
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56
                                            (coe v1))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         C_notFun_1012
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56
                                            (coe v1))
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe
                                         C_isEff_1010 (coe v6) (coe v8) (coe v2) (coe v3) (coe v4)
                                         (coe v5)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    C_notFun_1012
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6
               -> coe
                    C_notFun_1012
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    C_notFun_1012
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    C_notFun_1012
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    C_notFun_1012
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    C_notFun_1012
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_56 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_254 v1 -> coe C_notFun_1012 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.IntProjection
d_IntProjection_1084 a0 a1 = ()
data T_IntProjection_1084
  = C_isInt_1092 MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 Integer Integer |
    C_notInt_1094 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asInt
d_asInt_1100 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  T_InferElabResult_238 -> T_IntProjection_1084
d_asInt_1100 ~v0 ~v1 v2 = du_asInt_1100 v2
du_asInt_1100 :: T_InferElabResult_238 -> T_IntProjection_1084
du_asInt_1100 v0
  = case coe v0 of
      C_success_252 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    C_notInt_1094
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    C_notInt_1094
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> coe
                    C_notInt_1094
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    C_notInt_1094
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> coe
                    C_notInt_1094
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    C_notInt_1094
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6
               -> coe
                    C_notInt_1094
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe C_isInt_1092 (coe v2) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    C_notInt_1094
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    C_notInt_1094
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    C_notInt_1094
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_254 v1 -> coe C_notInt_1094 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.decideLeq
d_decideLeq_1134 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decideLeq_1134 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Zero_6
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased)
      MAlonzo.Code.Once.Type.C_One_8
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_One_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Many_10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_One_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.PolyBuiltinApp
d_PolyBuiltinApp_1136 = ()
data T_PolyBuiltinApp_1136
  = C_pba'45'id_1138 | C_pba'45'fst_1140 | C_pba'45'snd_1142 |
    C_pba'45'terminal_1144 | C_pba'45'inl_1146 | C_pba'45'inr_1148 |
    C_pba'45'initial_1150 | C_pba'45'arr_1152 |
    C_pba'45'pair'45'applied_1154 | C_pba'45'compose'45'applied_1156 |
    C_pba'45'curry_1158 | C_pba'45'apply_1160
-- Once.TypeCheck.Elaborate.classifyAppHead
d_classifyAppHead_1162 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe T_PolyBuiltinApp_1136
d_classifyAppHead_1162 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v1
        -> let v2
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v2 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                        (coe ("id" :: Data.Text.Text))) in
           coe
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
                  -> if coe v3
                       then coe
                              seq (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'id_1138))
                       else coe
                              seq (coe v4)
                              (let v5
                                     = coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v5 ->
                                            coe
                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                              (coe v1))
                                         (coe
                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                            (coe v1) (coe ("fst" :: Data.Text.Text))) in
                               coe
                                 (case coe v5 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                                      -> if coe v6
                                           then coe
                                                  seq (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                     (coe C_pba'45'fst_1140))
                                           else coe
                                                  seq (coe v7)
                                                  (let v8
                                                         = coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                             erased
                                                             (\ v8 ->
                                                                coe
                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                  (coe v1))
                                                             (coe
                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                (coe v1)
                                                                (coe ("snd" :: Data.Text.Text))) in
                                                   coe
                                                     (case coe v8 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                          -> if coe v9
                                                               then coe
                                                                      seq (coe v10)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                         (coe C_pba'45'snd_1142))
                                                               else coe
                                                                      seq (coe v10)
                                                                      (let v11
                                                                             = coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                 erased
                                                                                 (\ v11 ->
                                                                                    coe
                                                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                      (coe v1))
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                    (coe v1)
                                                                                    (coe
                                                                                       ("terminal"
                                                                                        ::
                                                                                        Data.Text.Text))) in
                                                                       coe
                                                                         (case coe v11 of
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                                              -> if coe v12
                                                                                   then coe
                                                                                          seq
                                                                                          (coe v13)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                             (coe
                                                                                                C_pba'45'terminal_1144))
                                                                                   else coe
                                                                                          seq
                                                                                          (coe v13)
                                                                                          (let v14
                                                                                                 = coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                     erased
                                                                                                     (\ v14 ->
                                                                                                        coe
                                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                          (coe
                                                                                                             v1))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                        (coe
                                                                                                           v1)
                                                                                                        (coe
                                                                                                           ("inl"
                                                                                                            ::
                                                                                                            Data.Text.Text))) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v14 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                                                  -> if coe
                                                                                                          v15
                                                                                                       then coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v16)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                 (coe
                                                                                                                    C_pba'45'inl_1146))
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v16)
                                                                                                              (let v17
                                                                                                                     = coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                         erased
                                                                                                                         (\ v17 ->
                                                                                                                            coe
                                                                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                              (coe
                                                                                                                                 v1))
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                            (coe
                                                                                                                               v1)
                                                                                                                            (coe
                                                                                                                               ("inr"
                                                                                                                                ::
                                                                                                                                Data.Text.Text))) in
                                                                                                               coe
                                                                                                                 (case coe
                                                                                                                         v17 of
                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                                      -> if coe
                                                                                                                              v18
                                                                                                                           then coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v19)
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                     (coe
                                                                                                                                        C_pba'45'inr_1148))
                                                                                                                           else coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v19)
                                                                                                                                  (let v20
                                                                                                                                         = coe
                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                             erased
                                                                                                                                             (\ v20 ->
                                                                                                                                                coe
                                                                                                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                  (coe
                                                                                                                                                     v1))
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                (coe
                                                                                                                                                   v1)
                                                                                                                                                (coe
                                                                                                                                                   ("initial"
                                                                                                                                                    ::
                                                                                                                                                    Data.Text.Text))) in
                                                                                                                                   coe
                                                                                                                                     (case coe
                                                                                                                                             v20 of
                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                                                                                          -> if coe
                                                                                                                                                  v21
                                                                                                                                               then coe
                                                                                                                                                      seq
                                                                                                                                                      (coe
                                                                                                                                                         v22)
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                         (coe
                                                                                                                                                            C_pba'45'initial_1150))
                                                                                                                                               else coe
                                                                                                                                                      seq
                                                                                                                                                      (coe
                                                                                                                                                         v22)
                                                                                                                                                      (let v23
                                                                                                                                                             = coe
                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                 erased
                                                                                                                                                                 (\ v23 ->
                                                                                                                                                                    coe
                                                                                                                                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                      (coe
                                                                                                                                                                         v1))
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                    (coe
                                                                                                                                                                       v1)
                                                                                                                                                                    (coe
                                                                                                                                                                       ("arr"
                                                                                                                                                                        ::
                                                                                                                                                                        Data.Text.Text))) in
                                                                                                                                                       coe
                                                                                                                                                         (case coe
                                                                                                                                                                 v23 of
                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                                                                                              -> if coe
                                                                                                                                                                      v24
                                                                                                                                                                   then coe
                                                                                                                                                                          seq
                                                                                                                                                                          (coe
                                                                                                                                                                             v25)
                                                                                                                                                                          (coe
                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                             (coe
                                                                                                                                                                                C_pba'45'arr_1152))
                                                                                                                                                                   else coe
                                                                                                                                                                          seq
                                                                                                                                                                          (coe
                                                                                                                                                                             v25)
                                                                                                                                                                          (let v26
                                                                                                                                                                                 = coe
                                                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                     erased
                                                                                                                                                                                     (\ v26 ->
                                                                                                                                                                                        coe
                                                                                                                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                          (coe
                                                                                                                                                                                             v1))
                                                                                                                                                                                     (coe
                                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                        (coe
                                                                                                                                                                                           v1)
                                                                                                                                                                                        (coe
                                                                                                                                                                                           ("curry"
                                                                                                                                                                                            ::
                                                                                                                                                                                            Data.Text.Text))) in
                                                                                                                                                                           coe
                                                                                                                                                                             (case coe
                                                                                                                                                                                     v26 of
                                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                                                                                  -> if coe
                                                                                                                                                                                          v27
                                                                                                                                                                                       then coe
                                                                                                                                                                                              seq
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 v28)
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    C_pba'45'curry_1158))
                                                                                                                                                                                       else coe
                                                                                                                                                                                              seq
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 v28)
                                                                                                                                                                                              (let v29
                                                                                                                                                                                                     = coe
                                                                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                         erased
                                                                                                                                                                                                         (\ v29 ->
                                                                                                                                                                                                            coe
                                                                                                                                                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v1))
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               v1)
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               ("apply"
                                                                                                                                                                                                                ::
                                                                                                                                                                                                                Data.Text.Text))) in
                                                                                                                                                                                               coe
                                                                                                                                                                                                 (case coe
                                                                                                                                                                                                         v29 of
                                                                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                                                                                                                      -> if coe
                                                                                                                                                                                                              v30
                                                                                                                                                                                                           then coe
                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v31)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        C_pba'45'apply_1160))
                                                                                                                                                                                                           else coe
                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v31)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v4 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v3))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v3)
                               (coe ("pair" :: Data.Text.Text))) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe C_pba'45'pair'45'applied_1154))
                              else coe
                                     seq (coe v6)
                                     (let v7
                                            = coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                erased
                                                (\ v7 ->
                                                   coe
                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                     (coe v3))
                                                (coe
                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                   (coe v3) (coe ("compose" :: Data.Text.Text))) in
                                      coe
                                        (case coe v7 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                             -> if coe v8
                                                  then coe
                                                         seq (coe v9)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                            (coe C_pba'45'compose'45'applied_1156))
                                                  else coe
                                                         seq (coe v9)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v3 v4 v5 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v1 v2 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppHeadView
d_AppHeadView_1264 a0 = ()
data T_AppHeadView_1264
  = C_ahv'45'id_1266 | C_ahv'45'fst_1268 | C_ahv'45'snd_1270 |
    C_ahv'45'terminal_1272 | C_ahv'45'inl_1274 | C_ahv'45'inr_1276 |
    C_ahv'45'initial_1278 | C_ahv'45'arr_1280 | C_ahv'45'curry_1282 |
    C_ahv'45'apply_1284 | C_ahv'45'pair'45'applied_1288 |
    C_ahv'45'compose'45'applied_1292 | C_ahv'45'other_1296
-- Once.TypeCheck.Elaborate.classifyAppHeadView
d_classifyAppHeadView_1300 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppHeadView_1264
d_classifyAppHeadView_1300 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v1
        -> let v2
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v2 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                        (coe ("id" :: Data.Text.Text))) in
           coe
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
                  -> if coe v3
                       then coe seq (coe v4) (coe C_ahv'45'id_1266)
                       else coe
                              seq (coe v4)
                              (let v5
                                     = coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v5 ->
                                            coe
                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                              (coe v1))
                                         (coe
                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                            (coe v1) (coe ("fst" :: Data.Text.Text))) in
                               coe
                                 (case coe v5 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                                      -> if coe v6
                                           then coe seq (coe v7) (coe C_ahv'45'fst_1268)
                                           else coe
                                                  seq (coe v7)
                                                  (let v8
                                                         = coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                             erased
                                                             (\ v8 ->
                                                                coe
                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                  (coe v1))
                                                             (coe
                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                (coe v1)
                                                                (coe ("snd" :: Data.Text.Text))) in
                                                   coe
                                                     (case coe v8 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                          -> if coe v9
                                                               then coe
                                                                      seq (coe v10)
                                                                      (coe C_ahv'45'snd_1270)
                                                               else coe
                                                                      seq (coe v10)
                                                                      (let v11
                                                                             = coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                 erased
                                                                                 (\ v11 ->
                                                                                    coe
                                                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                      (coe v1))
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                    (coe v1)
                                                                                    (coe
                                                                                       ("terminal"
                                                                                        ::
                                                                                        Data.Text.Text))) in
                                                                       coe
                                                                         (case coe v11 of
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                                              -> if coe v12
                                                                                   then coe
                                                                                          seq
                                                                                          (coe v13)
                                                                                          (coe
                                                                                             C_ahv'45'terminal_1272)
                                                                                   else coe
                                                                                          seq
                                                                                          (coe v13)
                                                                                          (let v14
                                                                                                 = coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                     erased
                                                                                                     (\ v14 ->
                                                                                                        coe
                                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                          (coe
                                                                                                             v1))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                        (coe
                                                                                                           v1)
                                                                                                        (coe
                                                                                                           ("inl"
                                                                                                            ::
                                                                                                            Data.Text.Text))) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v14 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                                                  -> if coe
                                                                                                          v15
                                                                                                       then coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v16)
                                                                                                              (coe
                                                                                                                 C_ahv'45'inl_1274)
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v16)
                                                                                                              (let v17
                                                                                                                     = coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                         erased
                                                                                                                         (\ v17 ->
                                                                                                                            coe
                                                                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                              (coe
                                                                                                                                 v1))
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                            (coe
                                                                                                                               v1)
                                                                                                                            (coe
                                                                                                                               ("inr"
                                                                                                                                ::
                                                                                                                                Data.Text.Text))) in
                                                                                                               coe
                                                                                                                 (case coe
                                                                                                                         v17 of
                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                                      -> if coe
                                                                                                                              v18
                                                                                                                           then coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v19)
                                                                                                                                  (coe
                                                                                                                                     C_ahv'45'inr_1276)
                                                                                                                           else coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v19)
                                                                                                                                  (let v20
                                                                                                                                         = coe
                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                             erased
                                                                                                                                             (\ v20 ->
                                                                                                                                                coe
                                                                                                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                  (coe
                                                                                                                                                     v1))
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                (coe
                                                                                                                                                   v1)
                                                                                                                                                (coe
                                                                                                                                                   ("initial"
                                                                                                                                                    ::
                                                                                                                                                    Data.Text.Text))) in
                                                                                                                                   coe
                                                                                                                                     (case coe
                                                                                                                                             v20 of
                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                                                                                          -> if coe
                                                                                                                                                  v21
                                                                                                                                               then coe
                                                                                                                                                      seq
                                                                                                                                                      (coe
                                                                                                                                                         v22)
                                                                                                                                                      (coe
                                                                                                                                                         C_ahv'45'initial_1278)
                                                                                                                                               else coe
                                                                                                                                                      seq
                                                                                                                                                      (coe
                                                                                                                                                         v22)
                                                                                                                                                      (let v23
                                                                                                                                                             = coe
                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                 erased
                                                                                                                                                                 (\ v23 ->
                                                                                                                                                                    coe
                                                                                                                                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                      (coe
                                                                                                                                                                         v1))
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                    (coe
                                                                                                                                                                       v1)
                                                                                                                                                                    (coe
                                                                                                                                                                       ("arr"
                                                                                                                                                                        ::
                                                                                                                                                                        Data.Text.Text))) in
                                                                                                                                                       coe
                                                                                                                                                         (case coe
                                                                                                                                                                 v23 of
                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                                                                                              -> if coe
                                                                                                                                                                      v24
                                                                                                                                                                   then coe
                                                                                                                                                                          seq
                                                                                                                                                                          (coe
                                                                                                                                                                             v25)
                                                                                                                                                                          (coe
                                                                                                                                                                             C_ahv'45'arr_1280)
                                                                                                                                                                   else coe
                                                                                                                                                                          seq
                                                                                                                                                                          (coe
                                                                                                                                                                             v25)
                                                                                                                                                                          (let v26
                                                                                                                                                                                 = coe
                                                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                     erased
                                                                                                                                                                                     (\ v26 ->
                                                                                                                                                                                        coe
                                                                                                                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                          (coe
                                                                                                                                                                                             v1))
                                                                                                                                                                                     (coe
                                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                        (coe
                                                                                                                                                                                           v1)
                                                                                                                                                                                        (coe
                                                                                                                                                                                           ("curry"
                                                                                                                                                                                            ::
                                                                                                                                                                                            Data.Text.Text))) in
                                                                                                                                                                           coe
                                                                                                                                                                             (case coe
                                                                                                                                                                                     v26 of
                                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                                                                                  -> if coe
                                                                                                                                                                                          v27
                                                                                                                                                                                       then coe
                                                                                                                                                                                              seq
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 v28)
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 C_ahv'45'curry_1282)
                                                                                                                                                                                       else coe
                                                                                                                                                                                              seq
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 v28)
                                                                                                                                                                                              (let v29
                                                                                                                                                                                                     = coe
                                                                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                         erased
                                                                                                                                                                                                         (\ v29 ->
                                                                                                                                                                                                            coe
                                                                                                                                                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v1))
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               v1)
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               ("apply"
                                                                                                                                                                                                                ::
                                                                                                                                                                                                                Data.Text.Text))) in
                                                                                                                                                                                               coe
                                                                                                                                                                                                 (case coe
                                                                                                                                                                                                         v29 of
                                                                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                                                                                                                      -> if coe
                                                                                                                                                                                                              v30
                                                                                                                                                                                                           then coe
                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v31)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     C_ahv'45'apply_1284)
                                                                                                                                                                                                           else coe
                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v31)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     C_ahv'45'other_1296)
                                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2
        -> coe C_ahv'45'other_1296
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v4 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v3))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v3)
                               (coe ("pair" :: Data.Text.Text))) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe seq (coe v6) (coe C_ahv'45'pair'45'applied_1288)
                              else coe
                                     seq (coe v6)
                                     (let v7
                                            = coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                erased
                                                (\ v7 ->
                                                   coe
                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                     (coe v3))
                                                (coe
                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                   (coe v3) (coe ("compose" :: Data.Text.Text))) in
                                      coe
                                        (case coe v7 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                             -> if coe v8
                                                  then coe
                                                         seq (coe v9)
                                                         (coe C_ahv'45'compose'45'applied_1292)
                                                  else coe seq (coe v9) (coe C_ahv'45'other_1296)
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v3 v4
               -> coe C_ahv'45'other_1296
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v3 v4
               -> coe C_ahv'45'other_1296
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v3 v4
               -> coe C_ahv'45'other_1296
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v3 v4 v5
               -> coe C_ahv'45'other_1296
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v3 v4
               -> coe C_ahv'45'other_1296
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v3 v4 v5 v6 v7
               -> coe C_ahv'45'other_1296
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
               -> coe C_ahv'45'other_1296
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v3
               -> coe C_ahv'45'other_1296
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v3
               -> coe C_ahv'45'other_1296
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v3 v4
               -> coe C_ahv'45'other_1296
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v3 v4 v5
               -> coe C_ahv'45'other_1296
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v4
               -> coe C_ahv'45'other_1296
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v1 v2
        -> coe C_ahv'45'other_1296
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v1 v2 v3
        -> coe C_ahv'45'other_1296
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v1 v2
        -> coe C_ahv'45'other_1296
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v1 v2 v3 v4 v5
        -> coe C_ahv'45'other_1296
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe C_ahv'45'other_1296
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v1
        -> coe C_ahv'45'other_1296
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v1
        -> coe C_ahv'45'other_1296
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v1 v2
        -> coe C_ahv'45'other_1296
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v1 v2 v3
        -> coe C_ahv'45'other_1296
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v2
        -> coe C_ahv'45'other_1296
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.classifyAppHead-nothing⇒view-other
d_classifyAppHead'45'nothing'8658'view'45'other_1404 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHead'45'nothing'8658'view'45'other_1404 = erased
-- Once.TypeCheck.Elaborate.composeArgB
d_composeArgB_1650 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeArgB_1650 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
           -> let v5
                    = let v5 = d_lookupPoly_288 (coe d_polys_434 (coe v0)) (coe v4) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                    -> coe
                                         MAlonzo.Code.Once.Type.d_schemaArrowCodomain_854 (coe v7)
                                         (coe v2)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                           _ -> MAlonzo.RTE.mazUnreachableError) in
              coe
                (case coe v4 of
                   l | (==) l ("fst" :: Data.Text.Text) ->
                       case coe v2 of
                         MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
                           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v6)
                         _ -> coe v5
                   l | (==) l ("id" :: Data.Text.Text) ->
                       coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                   l | (==) l ("snd" :: Data.Text.Text) ->
                       case coe v2 of
                         MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
                           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v7)
                         _ -> coe v5
                   l | (==) l ("terminal" :: Data.Text.Text) ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                         (coe MAlonzo.Code.Once.Type.C_Unit_118)
                   _ -> coe v5)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v8
                         -> case coe v8 of
                              l | (==) l ("compose" :: Data.Text.Text) ->
                                  let v9 = d_composeArgB_1650 (coe v0) (coe v5) (coe v2) in
                                  coe
                                    (case coe v9 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                         -> coe d_composeArgB_1650 (coe v0) (coe v7) (coe v10)
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v9
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v3
                       _ -> coe v3
                _ -> coe v3
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.BareBuiltinClass
d_BareBuiltinClass_1746 a0 = ()
data T_BareBuiltinClass_1746
  = C_bbc'45'id_1748 | C_bbc'45'fst_1750 | C_bbc'45'snd_1752 |
    C_bbc'45'terminal_1754 | C_bbc'45'initial_1756 |
    C_bbc'45'inl_1758 | C_bbc'45'inr_1760 | C_bbc'45'arr_1762 |
    C_bbc'45'other_1766
-- Once.TypeCheck.Elaborate.classifyBareBuiltin
d_classifyBareBuiltin_1770 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_BareBuiltinClass_1746
d_classifyBareBuiltin_1770 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v1 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                 (coe ("id" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
           -> if coe v2
                then coe seq (coe v3) (coe C_bbc'45'id_1748)
                else coe
                       seq (coe v3)
                       (let v4
                              = coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v4 ->
                                     coe
                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                       (coe v0))
                                  (coe
                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                                     (coe ("fst" :: Data.Text.Text))) in
                        coe
                          (case coe v4 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                               -> if coe v5
                                    then coe seq (coe v6) (coe C_bbc'45'fst_1750)
                                    else coe
                                           seq (coe v6)
                                           (let v7
                                                  = coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                      erased
                                                      (\ v7 ->
                                                         coe
                                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                           (coe v0))
                                                      (coe
                                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                         (coe v0)
                                                         (coe ("snd" :: Data.Text.Text))) in
                                            coe
                                              (case coe v7 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                                   -> if coe v8
                                                        then coe
                                                               seq (coe v9) (coe C_bbc'45'snd_1752)
                                                        else coe
                                                               seq (coe v9)
                                                               (let v10
                                                                      = coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                          erased
                                                                          (\ v10 ->
                                                                             coe
                                                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                               (coe v0))
                                                                          (coe
                                                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                             (coe v0)
                                                                             (coe
                                                                                ("terminal"
                                                                                 ::
                                                                                 Data.Text.Text))) in
                                                                coe
                                                                  (case coe v10 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                                       -> if coe v11
                                                                            then coe
                                                                                   seq (coe v12)
                                                                                   (coe
                                                                                      C_bbc'45'terminal_1754)
                                                                            else coe
                                                                                   seq (coe v12)
                                                                                   (let v13
                                                                                          = coe
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                              erased
                                                                                              (\ v13 ->
                                                                                                 coe
                                                                                                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                   (coe
                                                                                                      v0))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                 (coe
                                                                                                    v0)
                                                                                                 (coe
                                                                                                    ("initial"
                                                                                                     ::
                                                                                                     Data.Text.Text))) in
                                                                                    coe
                                                                                      (case coe
                                                                                              v13 of
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                                           -> if coe
                                                                                                   v14
                                                                                                then coe
                                                                                                       seq
                                                                                                       (coe
                                                                                                          v15)
                                                                                                       (coe
                                                                                                          C_bbc'45'initial_1756)
                                                                                                else coe
                                                                                                       seq
                                                                                                       (coe
                                                                                                          v15)
                                                                                                       (let v16
                                                                                                              = coe
                                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                  erased
                                                                                                                  (\ v16 ->
                                                                                                                     coe
                                                                                                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                       (coe
                                                                                                                          v0))
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                     (coe
                                                                                                                        v0)
                                                                                                                     (coe
                                                                                                                        ("inl"
                                                                                                                         ::
                                                                                                                         Data.Text.Text))) in
                                                                                                        coe
                                                                                                          (case coe
                                                                                                                  v16 of
                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                                                               -> if coe
                                                                                                                       v17
                                                                                                                    then coe
                                                                                                                           seq
                                                                                                                           (coe
                                                                                                                              v18)
                                                                                                                           (coe
                                                                                                                              C_bbc'45'inl_1758)
                                                                                                                    else coe
                                                                                                                           seq
                                                                                                                           (coe
                                                                                                                              v18)
                                                                                                                           (let v19
                                                                                                                                  = coe
                                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                      erased
                                                                                                                                      (\ v19 ->
                                                                                                                                         coe
                                                                                                                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                           (coe
                                                                                                                                              v0))
                                                                                                                                      (coe
                                                                                                                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                         (coe
                                                                                                                                            v0)
                                                                                                                                         (coe
                                                                                                                                            ("inr"
                                                                                                                                             ::
                                                                                                                                             Data.Text.Text))) in
                                                                                                                            coe
                                                                                                                              (case coe
                                                                                                                                      v19 of
                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                                                   -> if coe
                                                                                                                                           v20
                                                                                                                                        then coe
                                                                                                                                               seq
                                                                                                                                               (coe
                                                                                                                                                  v21)
                                                                                                                                               (coe
                                                                                                                                                  C_bbc'45'inr_1760)
                                                                                                                                        else coe
                                                                                                                                               seq
                                                                                                                                               (coe
                                                                                                                                                  v21)
                                                                                                                                               (let v22
                                                                                                                                                      = coe
                                                                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                          erased
                                                                                                                                                          (\ v22 ->
                                                                                                                                                             coe
                                                                                                                                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                               (coe
                                                                                                                                                                  v0))
                                                                                                                                                          (coe
                                                                                                                                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                             (coe
                                                                                                                                                                v0)
                                                                                                                                                             (coe
                                                                                                                                                                ("arr"
                                                                                                                                                                 ::
                                                                                                                                                                 Data.Text.Text))) in
                                                                                                                                                coe
                                                                                                                                                  (case coe
                                                                                                                                                          v22 of
                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                                                                                       -> if coe
                                                                                                                                                               v23
                                                                                                                                                            then coe
                                                                                                                                                                   seq
                                                                                                                                                                   (coe
                                                                                                                                                                      v24)
                                                                                                                                                                   (coe
                                                                                                                                                                      C_bbc'45'arr_1762)
                                                                                                                                                            else coe
                                                                                                                                                                   seq
                                                                                                                                                                   (coe
                                                                                                                                                                      v24)
                                                                                                                                                                   (coe
                                                                                                                                                                      C_bbc'45'other_1766)
                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_1840 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_238
d_inferElab_1840 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v3 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v2))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v2)
                        (coe ("unit" :: Data.Text.Text))) in
           coe
             (case coe v3 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                  -> if coe v4
                       then coe
                              seq (coe v5)
                              (coe
                                 C_success_252 (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                    (coe d_size_424 (coe v0)))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
                                 (coe (0 :: Integer)) (coe d_freshCounter_430 (coe v0)))
                       else coe
                              seq (coe v5)
                              (let v6
                                     = coe
                                         du_go_786 (coe v2) (coe d_size_424 (coe v0))
                                         (coe d_named_426 (coe v0)) (coe d_debruijn_428 (coe v0)) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                      -> case coe v7 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                             -> case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                    -> coe
                                                         C_success_252 (coe v8) (coe v10) (coe v11)
                                                         (coe (0 :: Integer))
                                                         (coe d_freshCounter_430 (coe v0))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> let v7
                                               = d_lookupImport_626
                                                   (coe d_imports_432 (coe v0)) (coe v2) in
                                         coe
                                           (case coe v7 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                -> coe
                                                     C_success_252 (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                        (coe d_size_424 (coe v0)))
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                        v2)
                                                     (coe (0 :: Integer))
                                                     (coe d_freshCounter_430 (coe v0))
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe
                                                     C_failure_254
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                        (coe v2))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> let v4
                 = d_lookupImport_626
                     (coe d_imports_432 (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("." :: Data.Text.Text) v2)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       C_success_252 (coe v5)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                          (coe d_size_424 (coe v0)))
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494 v2)
                       (coe (0 :: Integer)) (coe d_freshCounter_430 (coe v0))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       C_failure_254
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_UnboundQualified_14 (coe v2)
                          (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v2 v3
        -> let v4 = d_classifyAppHeadView_1300 (coe v2) in
           coe
             (case coe v4 of
                C_ahv'45'id_1266
                  -> let v5 = d_inferElab_1840 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_252 v6 v7 v8 v9 v10
                            -> coe
                                 C_success_252 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_424 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                    (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_424 (coe v0)))
                                    v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                       (coe d_debruijn_428 (coe v0))
                                       (coe
                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v6)
                                          (coe
                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                                          (coe v6))
                                       (coe du_specId_506))
                                    v8)
                                 (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                          C_failure_254 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'fst_1268
                  -> let v5 = d_inferElab_1840 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_252 v6 v7 v8 v9 v10
                            -> let v11
                                     = coe
                                         C_failure_254
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_30) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                                      -> coe
                                           C_success_252 (coe v12)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_424 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_424 (coe v0)))
                                              v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                 (coe d_debruijn_428 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                    (coe v12))
                                                 (coe du_specFst_514 (coe v13)))
                                              v8)
                                           (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                                    _ -> coe v11)
                          C_failure_254 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'snd_1270
                  -> let v5 = d_inferElab_1840 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_252 v6 v7 v8 v9 v10
                            -> let v11
                                     = coe
                                         C_failure_254
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_32) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                                      -> coe
                                           C_success_252 (coe v13)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_424 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_424 (coe v0)))
                                              v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                 (coe d_debruijn_428 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                    (coe v13))
                                                 (coe du_specSnd_524 (coe v12)))
                                              v8)
                                           (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                                    _ -> coe v11)
                          C_failure_254 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'terminal_1272
                  -> let v5 = d_inferElab_1840 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_252 v6 v7 v8 v9 v10
                            -> coe
                                 C_success_252 (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_424 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                    (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                       (coe d_size_424 (coe v0)))
                                    v7 v6 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                       (coe d_debruijn_428 (coe v0))
                                       (coe
                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v6)
                                          (coe
                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                                          (coe MAlonzo.Code.Once.Type.C_Unit_118))
                                       (coe du_specTerminal_568))
                                    v8)
                                 (coe addInt (coe (1 :: Integer)) (coe v9)) (coe v10)
                          C_failure_254 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'inl_1274
                  -> coe
                       C_failure_254
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_20)
                C_ahv'45'inr_1276
                  -> coe
                       C_failure_254
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_22)
                C_ahv'45'initial_1278
                  -> coe
                       C_failure_254
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_24)
                C_ahv'45'arr_1280
                  -> let v5 = d_inferElab_1840 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_252 v6 v7 v8 v9 v10
                            -> let v11
                                     = coe
                                         C_failure_254
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_ArrNeedsFunction_34) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                             -> case coe v15 of
                                                  MAlonzo.Code.Once.Type.C_Many_10
                                                    -> case coe v16 of
                                                         MAlonzo.Code.Once.Type.C_pure_34
                                                           -> coe
                                                                C_success_252
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                   (coe v12)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                      (coe v15)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_eff_36))
                                                                   (coe v14))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                      (coe d_size_424 (coe v0)))
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                      (coe v15) (coe v7)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                   (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                      (coe d_size_424 (coe v0)))
                                                                   v7
                                                                   (MAlonzo.Code.Once.Type.d__'8658'__146
                                                                      (coe v12) (coe v14))
                                                                   v15
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                      (coe d_debruijn_428 (coe v0))
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.d__'8658'__146
                                                                            (coe v12) (coe v14))
                                                                         (coe v13)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                            (coe v12)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe v15)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_eff_36))
                                                                            (coe v14)))
                                                                      (coe du_specArr_620))
                                                                   v8)
                                                                (coe
                                                                   addInt (coe (1 :: Integer))
                                                                   (coe v9))
                                                                (coe v10)
                                                         _ -> coe v11
                                                  _ -> coe v11
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> coe v11)
                          C_failure_254 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'curry_1282
                  -> coe
                       C_failure_254
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                          (coe ("curry" :: Data.Text.Text)))
                C_ahv'45'apply_1284
                  -> let v5 = d_inferElab_1840 (coe v0) (coe v3) in
                     coe
                       (case coe v5 of
                          C_success_252 v6 v7 v8 v9 v10
                            -> let v11
                                     = coe
                                         C_failure_254
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                            (coe ("apply" :: Data.Text.Text))) in
                               coe
                                 (case coe v6 of
                                    MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                                      -> case coe v12 of
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
                                             -> case coe v15 of
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                                    -> case coe v17 of
                                                         MAlonzo.Code.Once.Type.C_Many_10
                                                           -> case coe v18 of
                                                                MAlonzo.Code.Once.Type.C_pure_34
                                                                  -> let v19
                                                                           = d__'8799'T__176
                                                                               (coe v14)
                                                                               (coe v13) in
                                                                     coe
                                                                       (case coe v19 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                            -> if coe v20
                                                                                 then coe
                                                                                        seq
                                                                                        (coe v21)
                                                                                        (coe
                                                                                           C_success_252
                                                                                           (coe v16)
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                 (coe
                                                                                                    d_size_424
                                                                                                    (coe
                                                                                                       v0)))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                                 (coe
                                                                                                    v17)
                                                                                                 (coe
                                                                                                    v7)))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                 (coe
                                                                                                    d_size_424
                                                                                                    (coe
                                                                                                       v0)))
                                                                                              v7
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Type.C__'42'__122
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                    (coe
                                                                                                       v14)
                                                                                                    (coe
                                                                                                       v16))
                                                                                                 (coe
                                                                                                    v14))
                                                                                              v17
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                 (coe
                                                                                                    d_debruijn_428
                                                                                                    (coe
                                                                                                       v0))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Type.C__'42'__122
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                          (coe
                                                                                                             v14)
                                                                                                          (coe
                                                                                                             v16))
                                                                                                       (coe
                                                                                                          v14))
                                                                                                    (coe
                                                                                                       v15)
                                                                                                    (coe
                                                                                                       v16))
                                                                                                 (coe
                                                                                                    d_specApply_596
                                                                                                    (coe
                                                                                                       v14)
                                                                                                    (coe
                                                                                                       v16)))
                                                                                              v8)
                                                                                           (coe
                                                                                              addInt
                                                                                              (coe
                                                                                                 (1 ::
                                                                                                    Integer))
                                                                                              (coe
                                                                                                 v9))
                                                                                           (coe
                                                                                              v10))
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v21)
                                                                                        (coe
                                                                                           C_failure_254
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                              (coe
                                                                                                 ("apply"
                                                                                                  ::
                                                                                                  Data.Text.Text))))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                _ -> coe v11
                                                         _ -> coe v11
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> coe v11
                                    _ -> coe v11)
                          C_failure_254 v6 -> coe v5
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_ahv'45'pair'45'applied_1288
                  -> coe
                       C_failure_254
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                          (coe ("pair" :: Data.Text.Text)))
                C_ahv'45'compose'45'applied_1292
                  -> coe
                       C_failure_254
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                          (coe ("compose" :: Data.Text.Text)))
                C_ahv'45'other_1296
                  -> let v6
                           = coe du_asFun_1018 (coe d_inferElab_1840 (coe v0) (coe v2)) in
                     coe
                       (case coe v6 of
                          C_isFun_1002 v7 v8 v9 v10 v11 v12 v13
                            -> let v14 = d_checkElab_1846 (coe v0) (coe v3) (coe v7) in
                               coe
                                 (case coe v14 of
                                    C_success_276 v15 v16 v17 v18
                                      -> coe
                                           C_success_252 (coe v9)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe v8) (coe v15)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214 v10 v15 v7
                                              v8 v11 v16)
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v12)
                                              (coe v17))
                                           (coe v18)
                                    C_failure_278 v15 -> coe C_failure_254 (coe v15)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_isEff_1010 v7 v8 v9 v10 v11 v12
                            -> let v13 = d_checkElab_1846 (coe v0) (coe v3) (coe v7) in
                               coe
                                 (case coe v13 of
                                    C_success_276 v14 v15 v16 v17
                                      -> coe
                                           C_success_252
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                              (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_eff_36))
                                              (coe v8))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe v9) (coe v14))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_effApp_228 v9 v14
                                              v7 v10 v15)
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v11)
                                              (coe v16))
                                           (coe v17)
                                    C_failure_278 v14 -> coe C_failure_254 (coe v14)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          C_notFun_1012 v7 -> coe C_failure_254 (coe v7)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v2 v3
        -> coe
             C_failure_254
             (coe MAlonzo.Code.Once.TypeCheck.Error.C_LambdaInInferMode_16)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v2 v3 v4
        -> let v5 = d_inferElab_1840 (coe v0) (coe v3) in
           coe
             (case coe v5 of
                C_success_252 v6 v7 v8 v9 v10
                  -> let v11
                           = d_inferElab_1840
                               (coe d_extendNamedCtx_468 (coe v0) (coe v2) (coe v6)) (coe v4) in
                     coe
                       (case coe v11 of
                          C_success_252 v12 v13 v14 v15 v16
                            -> case coe v13 of
                                 MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v18 v19
                                   -> coe
                                        C_success_252 (coe v12)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                           (coe v19)
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                              (coe v18) (coe v7)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_let''_344 v7 v19 v18
                                           v6 v8 v14)
                                        (coe
                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v9)
                                           (coe addInt (coe (1 :: Integer)) (coe v15)))
                                        (coe v16)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          C_failure_254 v12 -> coe v11
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_254 v6 -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v2 v3
        -> let v4 = d_inferElab_1840 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                C_success_252 v5 v6 v7 v8 v9
                  -> let v10 = d_inferElab_1840 (coe v0) (coe v3) in
                     coe
                       (case coe v10 of
                          C_success_252 v11 v12 v13 v14 v15
                            -> coe
                                 C_success_252
                                 (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v5) (coe v11))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v6)
                                    (coe v12))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_242 v6 v12 v7 v13)
                                 (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v14))
                                 (coe v15)
                          C_failure_254 v11 -> coe v10
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_254 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v2 v3 v4 v5 v6
        -> let v7 = d_inferElab_1840 (coe v0) (coe v2) in
           coe
             (case coe v7 of
                C_success_252 v8 v9 v10 v11 v12
                  -> let v13
                           = coe
                               C_failure_254
                               (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_38) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Once.Type.C__'43'__124 v14 v15
                            -> let v16
                                     = d_inferElab_1840
                                         (coe d_extendNamedCtx_468 (coe v0) (coe v3) (coe v14))
                                         (coe v4) in
                               coe
                                 (case coe v16 of
                                    C_success_252 v17 v18 v19 v20 v21
                                      -> case coe v18 of
                                           MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v23 v24
                                             -> let v25
                                                      = d_inferElab_1840
                                                          (coe
                                                             d_extendNamedCtx_468 (coe v0) (coe v5)
                                                             (coe v15))
                                                          (coe v6) in
                                                coe
                                                  (case coe v25 of
                                                     C_success_252 v26 v27 v28 v29 v30
                                                       -> case coe v27 of
                                                            MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v32 v33
                                                              -> let v34
                                                                       = d__'8799'T__176
                                                                           (coe v17) (coe v26) in
                                                                 coe
                                                                   (case coe v34 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v35 v36
                                                                        -> if coe v35
                                                                             then coe
                                                                                    seq (coe v36)
                                                                                    (coe
                                                                                       C_success_252
                                                                                       (coe v26)
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                          (coe v9)
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Syntax.du__'8852''7512'__104
                                                                                             (coe
                                                                                                v24)
                                                                                             (coe
                                                                                                v33)))
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_case''_312
                                                                                          v9 v24 v33
                                                                                          v23 v32
                                                                                          v14 v15
                                                                                          v10 v19
                                                                                          v28)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                             (coe
                                                                                                v11)
                                                                                             (coe
                                                                                                addInt
                                                                                                (coe
                                                                                                   (1 ::
                                                                                                      Integer))
                                                                                                (coe
                                                                                                   v20)))
                                                                                          (coe
                                                                                             addInt
                                                                                             (coe
                                                                                                (1 ::
                                                                                                   Integer))
                                                                                             (coe
                                                                                                v29)))
                                                                                       (coe v30))
                                                                             else coe
                                                                                    seq (coe v36)
                                                                                    (coe
                                                                                       C_failure_254
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_CaseBranchMismatch_40))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     C_failure_254 v26 -> coe v25
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    C_failure_254 v17 -> coe v16
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> coe v13)
                C_failure_254 v8 -> coe v7
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe
             C_success_252 (coe MAlonzo.Code.Once.Type.C_Unit_118)
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_424 (coe v0)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
             (coe (0 :: Integer)) (coe d_freshCounter_430 (coe v0))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v2
        -> coe
             C_success_252 (coe MAlonzo.Code.Once.Type.C_Int_132)
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_424 (coe v0)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_int_350 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_430 (coe v0))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v2
        -> coe
             C_success_252 (coe MAlonzo.Code.Once.Type.C_Str_136)
             (coe
                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                (coe d_size_424 (coe v0)))
             (coe MAlonzo.Code.Once.Surface.Syntax.C_str_356 v2)
             (coe (0 :: Integer)) (coe d_freshCounter_430 (coe v0))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v2 v3
        -> let v4 = d_checkElab_1846 (coe v0) (coe v2) (coe v3) in
           coe
             (case coe v4 of
                C_success_276 v5 v6 v7 v8
                  -> coe C_success_252 (coe v3) (coe v5) (coe v6) (coe v7) (coe v8)
                C_failure_278 v5 -> coe C_failure_254 (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v2 v3 v4
        -> let v5
                 = coe du_asInt_1100 (coe d_inferElab_1840 (coe v0) (coe v3)) in
           coe
             (case coe v5 of
                C_isInt_1092 v6 v7 v8 v9
                  -> let v10
                           = coe du_asInt_1100 (coe d_inferElab_1840 (coe v0) (coe v4)) in
                     coe
                       (case coe v10 of
                          C_isInt_1092 v11 v12 v13 v14
                            -> coe
                                 MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                 (coe MAlonzo.Code.Once.TypeCheck.Raw.d_isArithmeticOp_90 (coe v2))
                                 (coe
                                    C_success_252 (coe MAlonzo.Code.Once.Type.C_Int_132)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v6)
                                       (coe v11))
                                    (coe du_mkArith_3040 v6 v11 v2 v7 v12)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v13))
                                    (coe v14))
                                 (coe
                                    C_success_252
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'43'__124
                                       (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                       (coe MAlonzo.Code.Once.Type.C_Unit_118))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80 (coe v6)
                                       (coe v11))
                                    (coe du_mkCmp_3048 v6 v11 v2 v7 v12)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v13))
                                    (coe v14))
                          C_notInt_1094 v11
                            -> coe
                                 C_failure_254
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_72
                                    (coe v11))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_notInt_1094 v6
                  -> coe
                       C_failure_254
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_70 (coe v6))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v3
        -> let v4 = d_inferElab_1840 (coe v0) (coe v3) in
           coe
             (case coe v4 of
                C_success_252 v5 v6 v7 v8 v9
                  -> let v10
                           = coe
                               C_failure_254
                               (coe MAlonzo.Code.Once.TypeCheck.Error.C_NegationNotInt_36) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Once.Type.C_Int_132
                            -> coe
                                 C_success_252 (coe v5) (coe v6)
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_414 v7) (coe v8)
                                 (coe v9)
                          _ -> coe v10)
                C_failure_254 v5 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_1846 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_262
d_checkElab_1846 v0 v1 v2
  = let v3
          = let v3 = d_inferElab_1840 (coe v0) (coe v1) in
            coe
              (case coe v3 of
                 C_success_252 v4 v5 v6 v7 v8
                   -> let v9 = d__'8799'T__176 (coe v2) (coe v4) in
                      coe
                        (case coe v9 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                             -> if coe v10
                                  then coe
                                         seq (coe v11)
                                         (coe C_success_276 (coe v5) (coe v6) (coe v7) (coe v8))
                                  else coe
                                         seq (coe v11)
                                         (coe
                                            C_failure_278
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                               (coe v2) (coe v4)))
                           _ -> MAlonzo.RTE.mazUnreachableError)
                 C_failure_254 v4 -> coe C_failure_278 (coe v4)
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
           -> coe d_checkElab'45'RVar_1854 (coe v0) (coe v4) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v4 v5
           -> let v6 = d_classifyAppHeadView_1300 (coe v4) in
              coe
                (case coe v6 of
                   C_ahv'45'id_1266
                     -> let v7 = d_inferElab_1840 (coe v0) (coe v5) in
                        coe
                          (case coe v7 of
                             C_success_252 v8 v9 v10 v11 v12
                               -> let v13
                                        = coe
                                            MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                            (coe
                                               MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                               (coe d_size_424 (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9)) in
                                  coe
                                    (let v14
                                           = coe
                                               MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                               (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                  (coe d_size_424 (coe v0)))
                                               v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                  (coe d_debruijn_428 (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                     (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                        (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                     (coe v8))
                                                  (coe du_specId_506))
                                               v10 in
                                     coe
                                       (let v15 = addInt (coe (1 :: Integer)) (coe v11) in
                                        coe
                                          (let v16 = d__'8799'T__176 (coe v2) (coe v8) in
                                           coe
                                             (case coe v16 of
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                  -> if coe v17
                                                       then coe
                                                              seq (coe v18)
                                                              (coe
                                                                 C_success_276 (coe v13) (coe v14)
                                                                 (coe v15) (coe v12))
                                                       else coe
                                                              seq (coe v18)
                                                              (coe
                                                                 C_failure_278
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                    (coe v2) (coe v8)))
                                                _ -> MAlonzo.RTE.mazUnreachableError))))
                             C_failure_254 v8
                               -> case coe v7 of
                                    C_success_252 v9 v10 v11 v12 v13
                                      -> let v14 = d__'8799'T__176 (coe v2) (coe v9) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                -> if coe v15
                                                     then coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_success_276 (coe v10) (coe v11)
                                                               (coe v12) (coe v13))
                                                     else coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_failure_278
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_254 v9 -> coe C_failure_278 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'fst_1268
                     -> let v7 = d_inferElab_1840 (coe v0) (coe v5) in
                        coe
                          (case coe v7 of
                             C_success_252 v8 v9 v10 v11 v12
                               -> case coe v8 of
                                    MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                      -> let v15
                                               = coe
                                                   MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                      (coe d_size_424 (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)) in
                                         coe
                                           (let v16
                                                  = coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                      (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                         (coe d_size_424 (coe v0)))
                                                      v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                         (coe d_debruijn_428 (coe v0))
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                            (coe v8)
                                                            (coe
                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_pure_34))
                                                            (coe v13))
                                                         (coe du_specFst_514 (coe v14)))
                                                      v10 in
                                            coe
                                              (let v17 = addInt (coe (1 :: Integer)) (coe v11) in
                                               coe
                                                 (let v18 = d__'8799'T__176 (coe v2) (coe v13) in
                                                  coe
                                                    (case coe v18 of
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                         -> if coe v19
                                                              then coe
                                                                     seq (coe v20)
                                                                     (coe
                                                                        C_success_276 (coe v15)
                                                                        (coe v16) (coe v17)
                                                                        (coe v12))
                                                              else coe
                                                                     seq (coe v20)
                                                                     (coe
                                                                        C_failure_278
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                           (coe v2) (coe v13)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError))))
                                    _ -> let v13
                                               = coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_30 in
                                         coe (coe C_failure_278 (coe v13))
                             C_failure_254 v8
                               -> case coe v7 of
                                    C_success_252 v9 v10 v11 v12 v13
                                      -> let v14 = d__'8799'T__176 (coe v2) (coe v9) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                -> if coe v15
                                                     then coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_success_276 (coe v10) (coe v11)
                                                               (coe v12) (coe v13))
                                                     else coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_failure_278
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_254 v9 -> coe C_failure_278 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'snd_1270
                     -> let v7 = d_inferElab_1840 (coe v0) (coe v5) in
                        coe
                          (case coe v7 of
                             C_success_252 v8 v9 v10 v11 v12
                               -> case coe v8 of
                                    MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                      -> let v15
                                               = coe
                                                   MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                      (coe d_size_424 (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)) in
                                         coe
                                           (let v16
                                                  = coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                      (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                         (coe d_size_424 (coe v0)))
                                                      v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                         (coe d_debruijn_428 (coe v0))
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                            (coe v8)
                                                            (coe
                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_pure_34))
                                                            (coe v14))
                                                         (coe du_specSnd_524 (coe v13)))
                                                      v10 in
                                            coe
                                              (let v17 = addInt (coe (1 :: Integer)) (coe v11) in
                                               coe
                                                 (let v18 = d__'8799'T__176 (coe v2) (coe v14) in
                                                  coe
                                                    (case coe v18 of
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                         -> if coe v19
                                                              then coe
                                                                     seq (coe v20)
                                                                     (coe
                                                                        C_success_276 (coe v15)
                                                                        (coe v16) (coe v17)
                                                                        (coe v12))
                                                              else coe
                                                                     seq (coe v20)
                                                                     (coe
                                                                        C_failure_278
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                           (coe v2) (coe v14)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError))))
                                    _ -> let v13
                                               = coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_32 in
                                         coe (coe C_failure_278 (coe v13))
                             C_failure_254 v8
                               -> case coe v7 of
                                    C_success_252 v9 v10 v11 v12 v13
                                      -> let v14 = d__'8799'T__176 (coe v2) (coe v9) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                -> if coe v15
                                                     then coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_success_276 (coe v10) (coe v11)
                                                               (coe v12) (coe v13))
                                                     else coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_failure_278
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_254 v9 -> coe C_failure_278 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'terminal_1272
                     -> let v7 = d_inferElab_1840 (coe v0) (coe v5) in
                        coe
                          (case coe v7 of
                             C_success_252 v8 v9 v10 v11 v12
                               -> let v13 = coe MAlonzo.Code.Once.Type.C_Unit_118 in
                                  coe
                                    (let v14
                                           = coe
                                               MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                  (coe d_size_424 (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe v9)) in
                                     coe
                                       (let v15
                                              = coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                  (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                     (coe d_size_424 (coe v0)))
                                                  v9 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                     (coe d_debruijn_428 (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                        (coe v8)
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                           (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                        (coe MAlonzo.Code.Once.Type.C_Unit_118))
                                                     (coe du_specTerminal_568))
                                                  v10 in
                                        coe
                                          (let v16 = addInt (coe (1 :: Integer)) (coe v11) in
                                           coe
                                             (let v17 = d__'8799'T__176 (coe v2) (coe v13) in
                                              coe
                                                (case coe v17 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                     -> if coe v18
                                                          then coe
                                                                 seq (coe v19)
                                                                 (coe
                                                                    C_success_276 (coe v14)
                                                                    (coe v15) (coe v16) (coe v12))
                                                          else coe
                                                                 seq (coe v19)
                                                                 (coe
                                                                    C_failure_278
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                       (coe v2) (coe v13)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError)))))
                             C_failure_254 v8
                               -> case coe v7 of
                                    C_success_252 v9 v10 v11 v12 v13
                                      -> let v14 = d__'8799'T__176 (coe v2) (coe v9) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                -> if coe v15
                                                     then coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_success_276 (coe v10) (coe v11)
                                                               (coe v12) (coe v13))
                                                     else coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_failure_278
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_254 v9 -> coe C_failure_278 (coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'inl_1274
                     -> case coe v2 of
                          MAlonzo.Code.Once.Type.C_Unit_118
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_Void_120
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C__'43'__124 v7 v8
                            -> let v9 = d_checkElab_1846 (coe v0) (coe v5) (coe v7) in
                               coe
                                 (case coe v9 of
                                    C_success_276 v10 v11 v12 v13
                                      -> coe
                                           C_success_276
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_424 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_424 (coe v0)))
                                              v10 v7 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                 (coe d_debruijn_428 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                    (coe v7)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                    (coe v2))
                                                 (coe du_specInl_534))
                                              v11)
                                           (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)
                                    C_failure_278 v10 -> coe v9
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v7 v8 v9
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_μ'45'type_128 v7
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_ν'45'type_130 v7
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_Int_132
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_Float_134
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_Str_136
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          MAlonzo.Code.Once.Type.C_Buffer_138
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_26)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_ahv'45'inr_1276
                     -> case coe v2 of
                          MAlonzo.Code.Once.Type.C_Unit_118
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_Void_120
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C__'43'__124 v7 v8
                            -> let v9 = d_checkElab_1846 (coe v0) (coe v5) (coe v8) in
                               coe
                                 (case coe v9 of
                                    C_success_276 v10 v11 v12 v13
                                      -> coe
                                           C_success_276
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_424 (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                 (coe d_size_424 (coe v0)))
                                              v10 v8 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                 (coe d_debruijn_428 (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                    (coe v2))
                                                 (coe du_specInr_544))
                                              v11)
                                           (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13)
                                    C_failure_278 v10 -> coe v9
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v7 v8 v9
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_μ'45'type_128 v7
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_ν'45'type_130 v7
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_Int_132
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_Float_134
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_Str_136
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          MAlonzo.Code.Once.Type.C_Buffer_138
                            -> coe
                                 C_failure_278
                                 (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_28)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_ahv'45'initial_1278
                     -> let v7
                              = d_checkElab_1846
                                  (coe v0) (coe v5) (coe MAlonzo.Code.Once.Type.C_Void_120) in
                        coe
                          (case coe v7 of
                             C_success_276 v8 v9 v10 v11
                               -> coe
                                    C_success_276
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                          (coe d_size_424 (coe v0)))
                                       (coe
                                          MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                       (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                          (coe d_size_424 (coe v0)))
                                       v8 (coe MAlonzo.Code.Once.Type.C_Void_120)
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                          (coe d_debruijn_428 (coe v0))
                                          (coe
                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                             (coe MAlonzo.Code.Once.Type.C_Void_120)
                                             (coe
                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                                             (coe v2))
                                          (coe du_specInitial_574))
                                       v9)
                                    (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11)
                             C_failure_278 v8 -> coe v7
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   C_ahv'45'arr_1280
                     -> case coe v2 of
                          MAlonzo.Code.Once.Type.C_Unit_118
                            -> coe
                                 C_failure_278
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_Void_120
                            -> coe
                                 C_failure_278
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
                            -> coe
                                 C_failure_278
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C__'43'__124 v7 v8
                            -> coe
                                 C_failure_278
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v7 v8 v9
                            -> case coe v8 of
                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50 v10 v11
                                   -> let v12
                                            = coe
                                                C_failure_278
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                   (coe v2) (coe v2)) in
                                      coe
                                        (case coe v10 of
                                           MAlonzo.Code.Once.Type.C_Many_10
                                             -> case coe v11 of
                                                  MAlonzo.Code.Once.Type.C_eff_36
                                                    -> let v13
                                                             = d_checkElab_1846
                                                                 (coe v0) (coe v5)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                    (coe v7)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                       (coe v10)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C_pure_34))
                                                                    (coe v9)) in
                                                       coe
                                                         (case coe v13 of
                                                            C_success_276 v14 v15 v16 v17
                                                              -> coe
                                                                   C_success_276
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                         (coe d_size_424 (coe v0)))
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                         (coe v10) (coe v14)))
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                      (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                         (coe d_size_424 (coe v0)))
                                                                      v14
                                                                      (MAlonzo.Code.Once.Type.d__'8658'__146
                                                                         (coe v7) (coe v9))
                                                                      v10
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                         (coe
                                                                            d_debruijn_428 (coe v0))
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.d__'8658'__146
                                                                               (coe v7) (coe v9))
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe v10)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_pure_34))
                                                                            (coe v2))
                                                                         (coe du_specArr_620))
                                                                      v15)
                                                                   (coe
                                                                      addInt (coe (1 :: Integer))
                                                                      (coe v16))
                                                                   (coe v17)
                                                            C_failure_278 v14 -> coe v13
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> coe v12
                                           _ -> coe v12)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Once.Type.C_μ'45'type_128 v7
                            -> coe
                                 C_failure_278
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_ν'45'type_130 v7
                            -> coe
                                 C_failure_278
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_Int_132
                            -> coe
                                 C_failure_278
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_Float_134
                            -> coe
                                 C_failure_278
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_Str_136
                            -> coe
                                 C_failure_278
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          MAlonzo.Code.Once.Type.C_Buffer_138
                            -> coe
                                 C_failure_278
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52 (coe v2)
                                    (coe v2))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_ahv'45'curry_1282
                     -> coe d_checkCurry_1882 (coe v0) (coe v5) (coe v2)
                   C_ahv'45'apply_1284
                     -> coe d_checkApply_1890 (coe v0) (coe v5) (coe v2)
                   C_ahv'45'pair'45'applied_1288
                     -> case coe v4 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v8 v9
                            -> coe
                                 d_checkPair_1864 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                       (coe ("pair" :: Data.Text.Text)))
                                    (coe v9))
                                 (coe v5) (coe v2)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_ahv'45'compose'45'applied_1292
                     -> case coe v4 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v8 v9
                            -> coe
                                 d_checkCompose_1874 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                       (coe ("compose" :: Data.Text.Text)))
                                    (coe v9))
                                 (coe v5) (coe v2)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   C_ahv'45'other_1296
                     -> let v8
                              = coe du_asFun_1018 (coe d_inferElab_1840 (coe v0) (coe v4)) in
                        coe
                          (case coe v8 of
                             C_isFun_1002 v9 v10 v11 v12 v13 v14 v15
                               -> let v16 = d_checkElab_1846 (coe v0) (coe v5) (coe v9) in
                                  coe
                                    (case coe v16 of
                                       C_success_276 v17 v18 v19 v20
                                         -> let v21
                                                  = coe
                                                      MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                      (coe v12)
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                         (coe v10) (coe v17)) in
                                            coe
                                              (let v22
                                                     = coe
                                                         MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                         v12 v17 v9 v10 v13 v18 in
                                               coe
                                                 (let v23
                                                        = MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                            (coe v14) (coe v19) in
                                                  coe
                                                    (let v24 = d__'8799'T__176 (coe v2) (coe v11) in
                                                     coe
                                                       (case coe v24 of
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                            -> if coe v25
                                                                 then coe
                                                                        seq (coe v26)
                                                                        (coe
                                                                           C_success_276 (coe v21)
                                                                           (coe v22) (coe v23)
                                                                           (coe v20))
                                                                 else coe
                                                                        seq (coe v26)
                                                                        (coe
                                                                           C_failure_278
                                                                           (coe
                                                                              MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                              (coe v2) (coe v11)))
                                                          _ -> MAlonzo.RTE.mazUnreachableError))))
                                       C_failure_278 v17
                                         -> let v18 = d_inferElab_1840 (coe v0) (coe v5) in
                                            coe
                                              (case coe v18 of
                                                 C_success_252 v19 v20 v21 v22 v23
                                                   -> let v24
                                                            = d_checkElab_1846
                                                                (coe v0) (coe v4)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                   (coe v19)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.d_pureK_58
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10))
                                                                   (coe v2)) in
                                                      coe
                                                        (case coe v24 of
                                                           C_success_276 v25 v26 v27 v28
                                                             -> coe
                                                                  C_success_276
                                                                  (coe
                                                                     MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                     (coe v25)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                        (coe v20)))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                     v25 v20 v19
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_Many_10)
                                                                     v26 v21)
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe
                                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                        (coe v27) (coe v22)))
                                                                  (coe v28)
                                                           C_failure_278 v25 -> coe v24
                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                 C_failure_254 v19 -> coe C_failure_278 (coe v19)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             C_isEff_1010 v9 v10 v11 v12 v13 v14
                               -> let v15 = d_checkElab_1846 (coe v0) (coe v5) (coe v9) in
                                  coe
                                    (case coe v15 of
                                       C_success_276 v16 v17 v18 v19
                                         -> let v20
                                                  = coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                      (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe MAlonzo.Code.Once.Type.C_eff_36))
                                                      (coe v10) in
                                            coe
                                              (let v21
                                                     = coe
                                                         MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                         (coe v11) (coe v16) in
                                               coe
                                                 (let v22
                                                        = coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_effApp_228
                                                            v11 v16 v9 v12 v17 in
                                                  coe
                                                    (let v23
                                                           = MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                               (coe v13) (coe v18) in
                                                     coe
                                                       (let v24
                                                              = d__'8799'T__176
                                                                  (coe v2) (coe v20) in
                                                        coe
                                                          (case coe v24 of
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                               -> if coe v25
                                                                    then coe
                                                                           seq (coe v26)
                                                                           (coe
                                                                              C_success_276
                                                                              (coe v21) (coe v22)
                                                                              (coe v23) (coe v19))
                                                                    else coe
                                                                           seq (coe v26)
                                                                           (coe
                                                                              C_failure_278
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                 (coe v2)
                                                                                 (coe v20)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError)))))
                                       C_failure_278 v16
                                         -> let v17 = d_inferElab_1840 (coe v0) (coe v5) in
                                            coe
                                              (case coe v17 of
                                                 C_success_252 v18 v19 v20 v21 v22
                                                   -> let v23
                                                            = d_checkElab_1846
                                                                (coe v0) (coe v4)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                   (coe v18)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.d_pureK_58
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10))
                                                                   (coe v2)) in
                                                      coe
                                                        (case coe v23 of
                                                           C_success_276 v24 v25 v26 v27
                                                             -> coe
                                                                  C_success_276
                                                                  (coe
                                                                     MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                     (coe v24)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                        (coe v19)))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                     v24 v19 v18
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_Many_10)
                                                                     v25 v20)
                                                                  (coe
                                                                     addInt (coe (1 :: Integer))
                                                                     (coe
                                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                        (coe v26) (coe v21)))
                                                                  (coe v27)
                                                           C_failure_278 v24 -> coe v23
                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                 C_failure_254 v18 -> coe C_failure_278 (coe v18)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             C_notFun_1012 v9
                               -> let v10 = d_inferElab_1840 (coe v0) (coe v5) in
                                  coe
                                    (case coe v10 of
                                       C_success_252 v11 v12 v13 v14 v15
                                         -> let v16
                                                  = d_checkElab_1846
                                                      (coe v0) (coe v4)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                         (coe v11)
                                                         (coe
                                                            MAlonzo.Code.Once.Type.d_pureK_58
                                                            (coe MAlonzo.Code.Once.Type.C_Many_10))
                                                         (coe v2)) in
                                            coe
                                              (case coe v16 of
                                                 C_success_276 v17 v18 v19 v20
                                                   -> coe
                                                        C_success_276
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                           (coe v17)
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                              (coe v12)))
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                           v17 v12 v11
                                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                           v18 v13)
                                                        (coe
                                                           addInt (coe (1 :: Integer))
                                                           (coe
                                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                              (coe v19) (coe v14)))
                                                        (coe v20)
                                                 C_failure_278 v17 -> coe v16
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       C_failure_254 v11 -> coe C_failure_278 (coe v11)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v4 v5
           -> let v6
                    = coe
                        C_failure_278
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Error.C_LambdaRequiresFunctionType_18) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v7 v8 v9
                     -> case coe v8 of
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50 v10 v11
                            -> case coe v11 of
                                 MAlonzo.Code.Once.Type.C_pure_34
                                   -> let v12
                                            = d_checkElab_1846
                                                (coe
                                                   d_extendNamedCtx_468 (coe v0) (coe v4) (coe v7))
                                                (coe v5) (coe v9) in
                                      coe
                                        (case coe v12 of
                                           C_success_276 v13 v14 v15 v16
                                             -> case coe v13 of
                                                  MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56 v18 v19
                                                    -> let v20
                                                             = d_decideLeq_1134
                                                                 (coe v18) (coe v10) in
                                                       coe
                                                         (case coe v20 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                                              -> coe
                                                                   C_success_276 (coe v19)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.C_lam_198
                                                                      v18 v14)
                                                                   (coe
                                                                      addInt (coe (1 :: Integer))
                                                                      (coe v15))
                                                                   (coe v16)
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe
                                                                   C_failure_278
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_64
                                                                      (coe v4) (coe v10) (coe v18))
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           C_failure_278 v13 -> coe v12
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> coe v6
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> coe v6)
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkElab-RVar
d_checkElab'45'RVar_1854 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_262
d_checkElab'45'RVar_1854 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v3 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v1))
              (coe
                 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                 (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                 (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)
                 (coe
                    MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                    ("id" :: Data.Text.Text))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then let v6 = seq (coe v5) (coe C_bbc'45'id_1748) in
                     coe
                       (case coe v6 of
                          C_bbc'45'id_1748
                            -> let v7 = "id" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_786 (coe ("id" :: Data.Text.Text))
                                            (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                            (coe d_debruijn_428 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_430 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__176
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_276
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_278
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_626
                                                      (coe d_imports_432 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_424 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_430
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__176
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_276
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_278
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_278 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                -> case coe v13 of
                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                                       -> case coe v15 of
                                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                                              -> case coe v16 of
                                                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                                                     -> let v17
                                                                                              = d__'8799'T__176
                                                                                                  (coe
                                                                                                     v12)
                                                                                                  (coe
                                                                                                     v14) in
                                                                                        coe
                                                                                          (case coe
                                                                                                  v17 of
                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                               -> if coe
                                                                                                       v18
                                                                                                    then coe
                                                                                                           seq
                                                                                                           (coe
                                                                                                              v19)
                                                                                                           (coe
                                                                                                              C_success_276
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                 (coe
                                                                                                                    d_size_424
                                                                                                                    (coe
                                                                                                                       v0)))
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                 (coe
                                                                                                                    d_debruijn_428
                                                                                                                    (coe
                                                                                                                       v0))
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                    (coe
                                                                                                                       v12)
                                                                                                                    (coe
                                                                                                                       v13)
                                                                                                                    (coe
                                                                                                                       v12))
                                                                                                                 (coe
                                                                                                                    du_specId_506))
                                                                                                              (coe
                                                                                                                 (0 ::
                                                                                                                    Integer))
                                                                                                              (coe
                                                                                                                 d_freshCounter_430
                                                                                                                 (coe
                                                                                                                    v0)))
                                                                                                    else coe
                                                                                                           seq
                                                                                                           (coe
                                                                                                              v19)
                                                                                                           (coe
                                                                                                              C_failure_278
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                 (coe
                                                                                                                    ("id"
                                                                                                                     ::
                                                                                                                     Data.Text.Text))))
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                   _ -> coe v11
                                                                            _ -> coe v11
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'fst_1750
                            -> let v7 = "fst" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_786 (coe ("fst" :: Data.Text.Text))
                                            (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                            (coe d_debruijn_428 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_430 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__176
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_276
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_278
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_626
                                                      (coe d_imports_432 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_424 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_430
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__176
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_276
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_278
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_278 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                -> case coe v12 of
                                                                     MAlonzo.Code.Once.Type.C__'42'__122 v15 v16
                                                                       -> case coe v13 of
                                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                                                              -> case coe v17 of
                                                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                                                     -> case coe
                                                                                               v18 of
                                                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                                                            -> let v19
                                                                                                     = d__'8799'T__176
                                                                                                         (coe
                                                                                                            v15)
                                                                                                         (coe
                                                                                                            v14) in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v19 of
                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                      -> if coe
                                                                                                              v20
                                                                                                           then coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v21)
                                                                                                                  (coe
                                                                                                                     C_success_276
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                        (coe
                                                                                                                           d_size_424
                                                                                                                           (coe
                                                                                                                              v0)))
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                        (coe
                                                                                                                           d_debruijn_428
                                                                                                                           (coe
                                                                                                                              v0))
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                           (coe
                                                                                                                              v12)
                                                                                                                           (coe
                                                                                                                              v13)
                                                                                                                           (coe
                                                                                                                              v15))
                                                                                                                        (coe
                                                                                                                           du_specFst_514
                                                                                                                           (coe
                                                                                                                              v16)))
                                                                                                                     (coe
                                                                                                                        (0 ::
                                                                                                                           Integer))
                                                                                                                     (coe
                                                                                                                        d_freshCounter_430
                                                                                                                        (coe
                                                                                                                           v0)))
                                                                                                           else coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v21)
                                                                                                                  (coe
                                                                                                                     C_failure_278
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                        (coe
                                                                                                                           ("fst"
                                                                                                                            ::
                                                                                                                            Data.Text.Text))))
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                          _ -> coe
                                                                                                 v11
                                                                                   _ -> coe v11
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'snd_1752
                            -> let v7 = "snd" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_786 (coe ("snd" :: Data.Text.Text))
                                            (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                            (coe d_debruijn_428 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_430 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__176
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_276
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_278
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_626
                                                      (coe d_imports_432 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_424 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_430
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__176
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_276
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_278
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_278 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                -> case coe v12 of
                                                                     MAlonzo.Code.Once.Type.C__'42'__122 v15 v16
                                                                       -> case coe v13 of
                                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                                                              -> case coe v17 of
                                                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                                                     -> case coe
                                                                                               v18 of
                                                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                                                            -> let v19
                                                                                                     = d__'8799'T__176
                                                                                                         (coe
                                                                                                            v16)
                                                                                                         (coe
                                                                                                            v14) in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v19 of
                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                      -> if coe
                                                                                                              v20
                                                                                                           then coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v21)
                                                                                                                  (coe
                                                                                                                     C_success_276
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                        (coe
                                                                                                                           d_size_424
                                                                                                                           (coe
                                                                                                                              v0)))
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                        (coe
                                                                                                                           d_debruijn_428
                                                                                                                           (coe
                                                                                                                              v0))
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                           (coe
                                                                                                                              v12)
                                                                                                                           (coe
                                                                                                                              v13)
                                                                                                                           (coe
                                                                                                                              v16))
                                                                                                                        (coe
                                                                                                                           du_specSnd_524
                                                                                                                           (coe
                                                                                                                              v15)))
                                                                                                                     (coe
                                                                                                                        (0 ::
                                                                                                                           Integer))
                                                                                                                     (coe
                                                                                                                        d_freshCounter_430
                                                                                                                        (coe
                                                                                                                           v0)))
                                                                                                           else coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v21)
                                                                                                                  (coe
                                                                                                                     C_failure_278
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                        (coe
                                                                                                                           ("snd"
                                                                                                                            ::
                                                                                                                            Data.Text.Text))))
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                          _ -> coe
                                                                                                 v11
                                                                                   _ -> coe v11
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'terminal_1754
                            -> let v7 = "terminal" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_786 (coe ("terminal" :: Data.Text.Text))
                                            (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                            (coe d_debruijn_428 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_430 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__176
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_276
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_278
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_626
                                                      (coe d_imports_432 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_424 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_430
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__176
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_276
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_278
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_278 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                -> case coe v13 of
                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                                       -> case coe v15 of
                                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                                              -> case coe v16 of
                                                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                                                     -> case coe
                                                                                               v14 of
                                                                                          MAlonzo.Code.Once.Type.C_Unit_118
                                                                                            -> coe
                                                                                                 C_success_276
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                    (coe
                                                                                                       d_size_424
                                                                                                       (coe
                                                                                                          v0)))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                    (coe
                                                                                                       d_debruijn_428
                                                                                                       (coe
                                                                                                          v0))
                                                                                                    (coe
                                                                                                       v2)
                                                                                                    (coe
                                                                                                       du_specTerminal_568))
                                                                                                 (coe
                                                                                                    (0 ::
                                                                                                       Integer))
                                                                                                 (coe
                                                                                                    d_freshCounter_430
                                                                                                    (coe
                                                                                                       v0))
                                                                                          _ -> coe
                                                                                                 v11
                                                                                   _ -> coe v11
                                                                            _ -> coe v11
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'initial_1756
                            -> let v7 = "initial" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_786 (coe ("initial" :: Data.Text.Text))
                                            (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                            (coe d_debruijn_428 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_430 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__176
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_276
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_278
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_626
                                                      (coe d_imports_432 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_424 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_430
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__176
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_276
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_278
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_278 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                -> case coe v12 of
                                                                     MAlonzo.Code.Once.Type.C_Void_120
                                                                       -> case coe v13 of
                                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                                              -> case coe v15 of
                                                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                                                     -> case coe
                                                                                               v16 of
                                                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                                                            -> coe
                                                                                                 C_success_276
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                    (coe
                                                                                                       d_size_424
                                                                                                       (coe
                                                                                                          v0)))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                    (coe
                                                                                                       d_debruijn_428
                                                                                                       (coe
                                                                                                          v0))
                                                                                                    (coe
                                                                                                       v2)
                                                                                                    (coe
                                                                                                       du_specInitial_574))
                                                                                                 (coe
                                                                                                    (0 ::
                                                                                                       Integer))
                                                                                                 (coe
                                                                                                    d_freshCounter_430
                                                                                                    (coe
                                                                                                       v0))
                                                                                          _ -> coe
                                                                                                 v11
                                                                                   _ -> coe v11
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'inl_1758
                            -> let v7 = "inl" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_786 (coe ("inl" :: Data.Text.Text))
                                            (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                            (coe d_debruijn_428 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_430 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__176
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_276
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_278
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_626
                                                      (coe d_imports_432 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_424 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_430
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__176
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_276
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_278
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_278 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                -> case coe v13 of
                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                                       -> case coe v15 of
                                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                                              -> case coe v16 of
                                                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                                                     -> case coe
                                                                                               v14 of
                                                                                          MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                                                                                            -> let v19
                                                                                                     = d__'8799'T__176
                                                                                                         (coe
                                                                                                            v12)
                                                                                                         (coe
                                                                                                            v17) in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v19 of
                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                      -> if coe
                                                                                                              v20
                                                                                                           then coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v21)
                                                                                                                  (coe
                                                                                                                     C_success_276
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                        (coe
                                                                                                                           d_size_424
                                                                                                                           (coe
                                                                                                                              v0)))
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                        (coe
                                                                                                                           d_debruijn_428
                                                                                                                           (coe
                                                                                                                              v0))
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                           (coe
                                                                                                                              v12)
                                                                                                                           (coe
                                                                                                                              v13)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Type.C__'43'__124
                                                                                                                              (coe
                                                                                                                                 v12)
                                                                                                                              (coe
                                                                                                                                 v18)))
                                                                                                                        (coe
                                                                                                                           du_specInl_534))
                                                                                                                     (coe
                                                                                                                        (0 ::
                                                                                                                           Integer))
                                                                                                                     (coe
                                                                                                                        d_freshCounter_430
                                                                                                                        (coe
                                                                                                                           v0)))
                                                                                                           else coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v21)
                                                                                                                  (coe
                                                                                                                     C_failure_278
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                        (coe
                                                                                                                           ("inl"
                                                                                                                            ::
                                                                                                                            Data.Text.Text))))
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                          _ -> coe
                                                                                                 v11
                                                                                   _ -> coe v11
                                                                            _ -> coe v11
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'inr_1760
                            -> let v7 = "inr" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_786 (coe ("inr" :: Data.Text.Text))
                                            (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                            (coe d_debruijn_428 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_430 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__176
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_276
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_278
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_626
                                                      (coe d_imports_432 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_424 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_430
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__176
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_276
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_278
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_278 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                -> case coe v13 of
                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                                       -> case coe v15 of
                                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                                              -> case coe v16 of
                                                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                                                     -> case coe
                                                                                               v14 of
                                                                                          MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                                                                                            -> let v19
                                                                                                     = d__'8799'T__176
                                                                                                         (coe
                                                                                                            v12)
                                                                                                         (coe
                                                                                                            v18) in
                                                                                               coe
                                                                                                 (case coe
                                                                                                         v19 of
                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                      -> if coe
                                                                                                              v20
                                                                                                           then coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v21)
                                                                                                                  (coe
                                                                                                                     C_success_276
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                        (coe
                                                                                                                           d_size_424
                                                                                                                           (coe
                                                                                                                              v0)))
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                        (coe
                                                                                                                           d_debruijn_428
                                                                                                                           (coe
                                                                                                                              v0))
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                           (coe
                                                                                                                              v12)
                                                                                                                           (coe
                                                                                                                              v13)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Type.C__'43'__124
                                                                                                                              (coe
                                                                                                                                 v17)
                                                                                                                              (coe
                                                                                                                                 v12)))
                                                                                                                        (coe
                                                                                                                           du_specInr_544))
                                                                                                                     (coe
                                                                                                                        (0 ::
                                                                                                                           Integer))
                                                                                                                     (coe
                                                                                                                        d_freshCounter_430
                                                                                                                        (coe
                                                                                                                           v0)))
                                                                                                           else coe
                                                                                                                  seq
                                                                                                                  (coe
                                                                                                                     v21)
                                                                                                                  (coe
                                                                                                                     C_failure_278
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                        (coe
                                                                                                                           ("inr"
                                                                                                                            ::
                                                                                                                            Data.Text.Text))))
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                          _ -> coe
                                                                                                 v11
                                                                                   _ -> coe v11
                                                                            _ -> coe v11
                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'arr_1762
                            -> let v7 = "arr" :: Data.Text.Text in
                               coe
                                 (let v8
                                        = coe
                                            du_go_786 (coe ("arr" :: Data.Text.Text))
                                            (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                            (coe d_debruijn_428 (coe v0)) in
                                  coe
                                    (case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                         -> case coe v9 of
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                -> case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> let v14 = 0 :: Integer in
                                                          coe
                                                            (let v15
                                                                   = d_freshCounter_430 (coe v0) in
                                                             coe
                                                               (let v16
                                                                      = d__'8799'T__176
                                                                          (coe v2) (coe v10) in
                                                                coe
                                                                  (case coe v16 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                       -> if coe v17
                                                                            then coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_success_276
                                                                                      (coe v12)
                                                                                      (coe v13)
                                                                                      (coe v14)
                                                                                      (coe v15))
                                                                            else coe
                                                                                   seq (coe v18)
                                                                                   (coe
                                                                                      C_failure_278
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                         (coe v2)
                                                                                         (coe v10)))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v9
                                                  = d_lookupImport_626
                                                      (coe d_imports_432 (coe v0)) (coe v7) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                   -> let v11
                                                            = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_424 (coe v0)) in
                                                      coe
                                                        (let v12
                                                               = coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                   v7 in
                                                         coe
                                                           (let v13 = 0 :: Integer in
                                                            coe
                                                              (let v14
                                                                     = d_freshCounter_430
                                                                         (coe v0) in
                                                               coe
                                                                 (let v15
                                                                        = d__'8799'T__176
                                                                            (coe v2) (coe v10) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                         -> if coe v16
                                                                              then coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_success_276
                                                                                        (coe v11)
                                                                                        (coe v12)
                                                                                        (coe v13)
                                                                                        (coe v14))
                                                                              else coe
                                                                                     seq (coe v17)
                                                                                     (coe
                                                                                        C_failure_278
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                           (coe v2)
                                                                                           (coe
                                                                                              v10)))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v10
                                                            = coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                (coe v7) in
                                                      coe
                                                        (let v11 = coe C_failure_278 (coe v10) in
                                                         coe
                                                           (case coe v2 of
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                -> case coe v12 of
                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                                                                       -> case coe v16 of
                                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                                                              -> case coe v18 of
                                                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                                                     -> case coe
                                                                                               v19 of
                                                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                                                            -> case coe
                                                                                                      v13 of
                                                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50 v20 v21
                                                                                                   -> case coe
                                                                                                             v20 of
                                                                                                        MAlonzo.Code.Once.Type.C_Many_10
                                                                                                          -> case coe
                                                                                                                    v21 of
                                                                                                               MAlonzo.Code.Once.Type.C_pure_34
                                                                                                                 -> case coe
                                                                                                                           v14 of
                                                                                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v22 v23 v24
                                                                                                                        -> case coe
                                                                                                                                  v23 of
                                                                                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                                                                                                                               -> case coe
                                                                                                                                         v25 of
                                                                                                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                                                                                                      -> case coe
                                                                                                                                                v26 of
                                                                                                                                           MAlonzo.Code.Once.Type.C_eff_36
                                                                                                                                             -> let v27
                                                                                                                                                      = d__'8799'T__176
                                                                                                                                                          (coe
                                                                                                                                                             v15)
                                                                                                                                                          (coe
                                                                                                                                                             v22) in
                                                                                                                                                coe
                                                                                                                                                  (let v28
                                                                                                                                                         = d__'8799'T__176
                                                                                                                                                             (coe
                                                                                                                                                                v17)
                                                                                                                                                             (coe
                                                                                                                                                                v24) in
                                                                                                                                                   coe
                                                                                                                                                     (case coe
                                                                                                                                                             v27 of
                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v29 v30
                                                                                                                                                          -> let v31
                                                                                                                                                                   = coe
                                                                                                                                                                       C_failure_278
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                                                                          (coe
                                                                                                                                                                             ("arr"
                                                                                                                                                                              ::
                                                                                                                                                                              Data.Text.Text))) in
                                                                                                                                                             coe
                                                                                                                                                               (case coe
                                                                                                                                                                       v29 of
                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                                                                    -> case coe
                                                                                                                                                                              v30 of
                                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v32
                                                                                                                                                                           -> case coe
                                                                                                                                                                                     v28 of
                                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                                                                                                  -> case coe
                                                                                                                                                                                            v33 of
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                                                                                         -> case coe
                                                                                                                                                                                                   v34 of
                                                                                                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v35
                                                                                                                                                                                                -> coe
                                                                                                                                                                                                     C_success_276
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           d_size_424
                                                                                                                                                                                                           (coe
                                                                                                                                                                                                              v0)))
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           d_debruijn_428
                                                                                                                                                                                                           (coe
                                                                                                                                                                                                              v0))
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                                                                                                           (coe
                                                                                                                                                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v15)
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                    v25)
                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                    v21))
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v17))
                                                                                                                                                                                                           (coe
                                                                                                                                                                                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v25)
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v21))
                                                                                                                                                                                                           (coe
                                                                                                                                                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v15)
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v23)
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v17)))
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           du_specArr_620))
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        (0 ::
                                                                                                                                                                                                           Integer))
                                                                                                                                                                                                     (coe
                                                                                                                                                                                                        d_freshCounter_430
                                                                                                                                                                                                        (coe
                                                                                                                                                                                                           v0))
                                                                                                                                                                                              _ -> coe
                                                                                                                                                                                                     v31
                                                                                                                                                                                       _ -> coe
                                                                                                                                                                                              v31
                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                         _ -> coe
                                                                                                                                                                                v31
                                                                                                                                                                  _ -> coe
                                                                                                                                                                         v31)
                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                           _ -> coe
                                                                                                                                                  v11
                                                                                                                                    _ -> coe
                                                                                                                                           v11
                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                      _ -> coe
                                                                                                                             v11
                                                                                                               _ -> coe
                                                                                                                      v11
                                                                                                        _ -> coe
                                                                                                               v11
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                          _ -> coe
                                                                                                 v11
                                                                                   _ -> coe v11
                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                     _ -> coe v11
                                                              _ -> coe v11))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                          C_bbc'45'other_1766
                            -> let v8
                                     = coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v8 ->
                                            coe
                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                              (coe v1))
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                            (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                               v1)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                               ("unit" :: Data.Text.Text))) in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                      -> if coe v9
                                           then let v11
                                                      = seq
                                                          (coe v10)
                                                          (coe
                                                             C_success_252
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                (coe d_size_424 (coe v0)))
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
                                                             (coe (0 :: Integer))
                                                             (coe d_freshCounter_430 (coe v0))) in
                                                coe
                                                  (case coe v11 of
                                                     C_success_252 v12 v13 v14 v15 v16
                                                       -> let v17
                                                                = d__'8799'T__176
                                                                    (coe v2) (coe v12) in
                                                          coe
                                                            (case coe v17 of
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                 -> if coe v18
                                                                      then coe
                                                                             seq (coe v19)
                                                                             (coe
                                                                                C_success_276
                                                                                (coe v13) (coe v14)
                                                                                (coe v15) (coe v16))
                                                                      else coe
                                                                             seq (coe v19)
                                                                             (coe
                                                                                C_failure_278
                                                                                (coe
                                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                   (coe v2)
                                                                                   (coe v12)))
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     C_failure_254 v12
                                                       -> let v13
                                                                = d_lookupPoly_288
                                                                    (coe d_polys_434 (coe v0))
                                                                    (coe v1) in
                                                          coe
                                                            (case coe v13 of
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                 -> coe
                                                                      C_success_276
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                         (coe d_size_424 (coe v0)))
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Syntax.C_poly_504
                                                                         v1)
                                                                      (coe (0 :: Integer))
                                                                      (coe
                                                                         d_freshCounter_430
                                                                         (coe v0))
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                 -> coe C_failure_278 (coe v12)
                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           else (let v11
                                                       = seq
                                                           (coe v10)
                                                           (let v11
                                                                  = coe
                                                                      du_go_786 (coe v1)
                                                                      (coe d_size_424 (coe v0))
                                                                      (coe d_named_426 (coe v0))
                                                                      (coe
                                                                         d_debruijn_428 (coe v0)) in
                                                            coe
                                                              (case coe v11 of
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                   -> case coe v12 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                          -> case coe v14 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                 -> coe
                                                                                      C_success_252
                                                                                      (coe v13)
                                                                                      (coe v15)
                                                                                      (coe v16)
                                                                                      (coe
                                                                                         (0 ::
                                                                                            Integer))
                                                                                      (coe
                                                                                         d_freshCounter_430
                                                                                         (coe v0))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                   -> let v12
                                                                            = d_lookupImport_626
                                                                                (coe
                                                                                   d_imports_432
                                                                                   (coe v0))
                                                                                (coe v1) in
                                                                      coe
                                                                        (case coe v12 of
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                             -> coe
                                                                                  C_success_252
                                                                                  (coe v13)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                     (coe
                                                                                        d_size_424
                                                                                        (coe v0)))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                                     v1)
                                                                                  (coe
                                                                                     (0 :: Integer))
                                                                                  (coe
                                                                                     d_freshCounter_430
                                                                                     (coe v0))
                                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                             -> coe
                                                                                  C_failure_254
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                                     (coe v1))
                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                 _ -> MAlonzo.RTE.mazUnreachableError)) in
                                                 coe
                                                   (case coe v11 of
                                                      C_success_252 v12 v13 v14 v15 v16
                                                        -> let v17
                                                                 = d__'8799'T__176
                                                                     (coe v2) (coe v12) in
                                                           coe
                                                             (case coe v17 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                  -> if coe v18
                                                                       then coe
                                                                              seq (coe v19)
                                                                              (coe
                                                                                 C_success_276
                                                                                 (coe v13) (coe v14)
                                                                                 (coe v15)
                                                                                 (coe v16))
                                                                       else coe
                                                                              seq (coe v19)
                                                                              (coe
                                                                                 C_failure_278
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                    (coe v2)
                                                                                    (coe v12)))
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      C_failure_254 v12
                                                        -> let v13
                                                                 = d_lookupPoly_288
                                                                     (coe d_polys_434 (coe v0))
                                                                     (coe v1) in
                                                           coe
                                                             (case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                  -> coe
                                                                       C_success_276
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                          (coe d_size_424 (coe v0)))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_poly_504
                                                                          v1)
                                                                       (coe (0 :: Integer))
                                                                       (coe
                                                                          d_freshCounter_430
                                                                          (coe v0))
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> coe C_failure_278 (coe v12)
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else (let v6
                            = seq
                                (coe v5)
                                (let v6
                                       = coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                           erased
                                           (\ v6 ->
                                              coe
                                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                (coe v1))
                                           (coe
                                              MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                              (coe v1) (coe ("fst" :: Data.Text.Text))) in
                                 coe
                                   (case coe v6 of
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                        -> if coe v7
                                             then coe seq (coe v8) (coe C_bbc'45'fst_1750)
                                             else coe
                                                    seq (coe v8)
                                                    (let v9
                                                           = coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                               erased
                                                               (\ v9 ->
                                                                  coe
                                                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                    (coe v1))
                                                               (coe
                                                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                  (coe v1)
                                                                  (coe
                                                                     ("snd" :: Data.Text.Text))) in
                                                     coe
                                                       (case coe v9 of
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                            -> if coe v10
                                                                 then coe
                                                                        seq (coe v11)
                                                                        (coe C_bbc'45'snd_1752)
                                                                 else coe
                                                                        seq (coe v11)
                                                                        (let v12
                                                                               = coe
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                   erased
                                                                                   (\ v12 ->
                                                                                      coe
                                                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                        (coe v1))
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                      (coe v1)
                                                                                      (coe
                                                                                         ("terminal"
                                                                                          ::
                                                                                          Data.Text.Text))) in
                                                                         coe
                                                                           (case coe v12 of
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                                                -> if coe v13
                                                                                     then coe
                                                                                            seq
                                                                                            (coe
                                                                                               v14)
                                                                                            (coe
                                                                                               C_bbc'45'terminal_1754)
                                                                                     else coe
                                                                                            seq
                                                                                            (coe
                                                                                               v14)
                                                                                            (let v15
                                                                                                   = coe
                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                       erased
                                                                                                       (\ v15 ->
                                                                                                          coe
                                                                                                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                            (coe
                                                                                                               v1))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                          (coe
                                                                                                             v1)
                                                                                                          (coe
                                                                                                             ("initial"
                                                                                                              ::
                                                                                                              Data.Text.Text))) in
                                                                                             coe
                                                                                               (case coe
                                                                                                       v15 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                                                    -> if coe
                                                                                                            v16
                                                                                                         then coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v17)
                                                                                                                (coe
                                                                                                                   C_bbc'45'initial_1756)
                                                                                                         else coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v17)
                                                                                                                (let v18
                                                                                                                       = coe
                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                           erased
                                                                                                                           (\ v18 ->
                                                                                                                              coe
                                                                                                                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                (coe
                                                                                                                                   v1))
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                              (coe
                                                                                                                                 v1)
                                                                                                                              (coe
                                                                                                                                 ("inl"
                                                                                                                                  ::
                                                                                                                                  Data.Text.Text))) in
                                                                                                                 coe
                                                                                                                   (case coe
                                                                                                                           v18 of
                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                                                                        -> if coe
                                                                                                                                v19
                                                                                                                             then coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v20)
                                                                                                                                    (coe
                                                                                                                                       C_bbc'45'inl_1758)
                                                                                                                             else coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v20)
                                                                                                                                    (let v21
                                                                                                                                           = coe
                                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                               erased
                                                                                                                                               (\ v21 ->
                                                                                                                                                  coe
                                                                                                                                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                    (coe
                                                                                                                                                       v1))
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                  (coe
                                                                                                                                                     v1)
                                                                                                                                                  (coe
                                                                                                                                                     ("inr"
                                                                                                                                                      ::
                                                                                                                                                      Data.Text.Text))) in
                                                                                                                                     coe
                                                                                                                                       (case coe
                                                                                                                                               v21 of
                                                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                                                                            -> if coe
                                                                                                                                                    v22
                                                                                                                                                 then coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v23)
                                                                                                                                                        (coe
                                                                                                                                                           C_bbc'45'inr_1760)
                                                                                                                                                 else coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v23)
                                                                                                                                                        (let v24
                                                                                                                                                               = coe
                                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                   erased
                                                                                                                                                                   (\ v24 ->
                                                                                                                                                                      coe
                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                        (coe
                                                                                                                                                                           v1))
                                                                                                                                                                   (coe
                                                                                                                                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                      (coe
                                                                                                                                                                         v1)
                                                                                                                                                                      (coe
                                                                                                                                                                         ("arr"
                                                                                                                                                                          ::
                                                                                                                                                                          Data.Text.Text))) in
                                                                                                                                                         coe
                                                                                                                                                           (case coe
                                                                                                                                                                   v24 of
                                                                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                                                                                                                -> if coe
                                                                                                                                                                        v25
                                                                                                                                                                     then coe
                                                                                                                                                                            seq
                                                                                                                                                                            (coe
                                                                                                                                                                               v26)
                                                                                                                                                                            (coe
                                                                                                                                                                               C_bbc'45'arr_1762)
                                                                                                                                                                     else coe
                                                                                                                                                                            seq
                                                                                                                                                                            (coe
                                                                                                                                                                               v26)
                                                                                                                                                                            (coe
                                                                                                                                                                               C_bbc'45'other_1766)
                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                      _ -> MAlonzo.RTE.mazUnreachableError)) in
                      coe
                        (case coe v6 of
                           C_bbc'45'id_1748
                             -> let v7 = "id" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_786 (coe ("id" :: Data.Text.Text))
                                             (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                             (coe d_debruijn_428 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_430 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__176
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_276
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_278
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_626
                                                       (coe d_imports_432 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_424 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_430
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__176
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_276
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_278
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_278 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                 -> case coe v13 of
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> case coe v16 of
                                                                                    MAlonzo.Code.Once.Type.C_pure_34
                                                                                      -> let v17
                                                                                               = d__'8799'T__176
                                                                                                   (coe
                                                                                                      v12)
                                                                                                   (coe
                                                                                                      v14) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v17 of
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                -> if coe
                                                                                                        v18
                                                                                                     then coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v19)
                                                                                                            (coe
                                                                                                               C_success_276
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                  (coe
                                                                                                                     d_size_424
                                                                                                                     (coe
                                                                                                                        v0)))
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                  (coe
                                                                                                                     d_debruijn_428
                                                                                                                     (coe
                                                                                                                        v0))
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                     (coe
                                                                                                                        v12)
                                                                                                                     (coe
                                                                                                                        v13)
                                                                                                                     (coe
                                                                                                                        v12))
                                                                                                                  (coe
                                                                                                                     du_specId_506))
                                                                                                               (coe
                                                                                                                  (0 ::
                                                                                                                     Integer))
                                                                                                               (coe
                                                                                                                  d_freshCounter_430
                                                                                                                  (coe
                                                                                                                     v0)))
                                                                                                     else coe
                                                                                                            seq
                                                                                                            (coe
                                                                                                               v19)
                                                                                                            (coe
                                                                                                               C_failure_278
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                  (coe
                                                                                                                     ("id"
                                                                                                                      ::
                                                                                                                      Data.Text.Text))))
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                    _ -> coe v11
                                                                             _ -> coe v11
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'fst_1750
                             -> let v7 = "fst" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_786 (coe ("fst" :: Data.Text.Text))
                                             (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                             (coe d_debruijn_428 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_430 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__176
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_276
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_278
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_626
                                                       (coe d_imports_432 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_424 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_430
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__176
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_276
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_278
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_278 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                 -> case coe v12 of
                                                                      MAlonzo.Code.Once.Type.C__'42'__122 v15 v16
                                                                        -> case coe v13 of
                                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                                                               -> case coe v17 of
                                                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                                                      -> case coe
                                                                                                v18 of
                                                                                           MAlonzo.Code.Once.Type.C_pure_34
                                                                                             -> let v19
                                                                                                      = d__'8799'T__176
                                                                                                          (coe
                                                                                                             v15)
                                                                                                          (coe
                                                                                                             v14) in
                                                                                                coe
                                                                                                  (case coe
                                                                                                          v19 of
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                       -> if coe
                                                                                                               v20
                                                                                                            then coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v21)
                                                                                                                   (coe
                                                                                                                      C_success_276
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                         (coe
                                                                                                                            d_size_424
                                                                                                                            (coe
                                                                                                                               v0)))
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                         (coe
                                                                                                                            d_debruijn_428
                                                                                                                            (coe
                                                                                                                               v0))
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                            (coe
                                                                                                                               v12)
                                                                                                                            (coe
                                                                                                                               v13)
                                                                                                                            (coe
                                                                                                                               v15))
                                                                                                                         (coe
                                                                                                                            du_specFst_514
                                                                                                                            (coe
                                                                                                                               v16)))
                                                                                                                      (coe
                                                                                                                         (0 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         d_freshCounter_430
                                                                                                                         (coe
                                                                                                                            v0)))
                                                                                                            else coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v21)
                                                                                                                   (coe
                                                                                                                      C_failure_278
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                         (coe
                                                                                                                            ("fst"
                                                                                                                             ::
                                                                                                                             Data.Text.Text))))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> coe
                                                                                                  v11
                                                                                    _ -> coe v11
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'snd_1752
                             -> let v7 = "snd" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_786 (coe ("snd" :: Data.Text.Text))
                                             (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                             (coe d_debruijn_428 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_430 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__176
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_276
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_278
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_626
                                                       (coe d_imports_432 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_424 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_430
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__176
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_276
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_278
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_278 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                 -> case coe v12 of
                                                                      MAlonzo.Code.Once.Type.C__'42'__122 v15 v16
                                                                        -> case coe v13 of
                                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                                                               -> case coe v17 of
                                                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                                                      -> case coe
                                                                                                v18 of
                                                                                           MAlonzo.Code.Once.Type.C_pure_34
                                                                                             -> let v19
                                                                                                      = d__'8799'T__176
                                                                                                          (coe
                                                                                                             v16)
                                                                                                          (coe
                                                                                                             v14) in
                                                                                                coe
                                                                                                  (case coe
                                                                                                          v19 of
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                       -> if coe
                                                                                                               v20
                                                                                                            then coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v21)
                                                                                                                   (coe
                                                                                                                      C_success_276
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                         (coe
                                                                                                                            d_size_424
                                                                                                                            (coe
                                                                                                                               v0)))
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                         (coe
                                                                                                                            d_debruijn_428
                                                                                                                            (coe
                                                                                                                               v0))
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                            (coe
                                                                                                                               v12)
                                                                                                                            (coe
                                                                                                                               v13)
                                                                                                                            (coe
                                                                                                                               v16))
                                                                                                                         (coe
                                                                                                                            du_specSnd_524
                                                                                                                            (coe
                                                                                                                               v15)))
                                                                                                                      (coe
                                                                                                                         (0 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         d_freshCounter_430
                                                                                                                         (coe
                                                                                                                            v0)))
                                                                                                            else coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v21)
                                                                                                                   (coe
                                                                                                                      C_failure_278
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                         (coe
                                                                                                                            ("snd"
                                                                                                                             ::
                                                                                                                             Data.Text.Text))))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> coe
                                                                                                  v11
                                                                                    _ -> coe v11
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'terminal_1754
                             -> let v7 = "terminal" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_786 (coe ("terminal" :: Data.Text.Text))
                                             (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                             (coe d_debruijn_428 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_430 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__176
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_276
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_278
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_626
                                                       (coe d_imports_432 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_424 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_430
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__176
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_276
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_278
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_278 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                 -> case coe v13 of
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> case coe v16 of
                                                                                    MAlonzo.Code.Once.Type.C_pure_34
                                                                                      -> case coe
                                                                                                v14 of
                                                                                           MAlonzo.Code.Once.Type.C_Unit_118
                                                                                             -> coe
                                                                                                  C_success_276
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                     (coe
                                                                                                        d_size_424
                                                                                                        (coe
                                                                                                           v0)))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                     (coe
                                                                                                        d_debruijn_428
                                                                                                        (coe
                                                                                                           v0))
                                                                                                     (coe
                                                                                                        v2)
                                                                                                     (coe
                                                                                                        du_specTerminal_568))
                                                                                                  (coe
                                                                                                     (0 ::
                                                                                                        Integer))
                                                                                                  (coe
                                                                                                     d_freshCounter_430
                                                                                                     (coe
                                                                                                        v0))
                                                                                           _ -> coe
                                                                                                  v11
                                                                                    _ -> coe v11
                                                                             _ -> coe v11
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'initial_1756
                             -> let v7 = "initial" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_786 (coe ("initial" :: Data.Text.Text))
                                             (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                             (coe d_debruijn_428 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_430 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__176
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_276
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_278
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_626
                                                       (coe d_imports_432 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_424 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_430
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__176
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_276
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_278
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_278 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                 -> case coe v12 of
                                                                      MAlonzo.Code.Once.Type.C_Void_120
                                                                        -> case coe v13 of
                                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                                               -> case coe v15 of
                                                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                                                      -> case coe
                                                                                                v16 of
                                                                                           MAlonzo.Code.Once.Type.C_pure_34
                                                                                             -> coe
                                                                                                  C_success_276
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                     (coe
                                                                                                        d_size_424
                                                                                                        (coe
                                                                                                           v0)))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                     (coe
                                                                                                        d_debruijn_428
                                                                                                        (coe
                                                                                                           v0))
                                                                                                     (coe
                                                                                                        v2)
                                                                                                     (coe
                                                                                                        du_specInitial_574))
                                                                                                  (coe
                                                                                                     (0 ::
                                                                                                        Integer))
                                                                                                  (coe
                                                                                                     d_freshCounter_430
                                                                                                     (coe
                                                                                                        v0))
                                                                                           _ -> coe
                                                                                                  v11
                                                                                    _ -> coe v11
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'inl_1758
                             -> let v7 = "inl" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_786 (coe ("inl" :: Data.Text.Text))
                                             (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                             (coe d_debruijn_428 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_430 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__176
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_276
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_278
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_626
                                                       (coe d_imports_432 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_424 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_430
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__176
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_276
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_278
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_278 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                 -> case coe v13 of
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> case coe v16 of
                                                                                    MAlonzo.Code.Once.Type.C_pure_34
                                                                                      -> case coe
                                                                                                v14 of
                                                                                           MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                                                                                             -> let v19
                                                                                                      = d__'8799'T__176
                                                                                                          (coe
                                                                                                             v12)
                                                                                                          (coe
                                                                                                             v17) in
                                                                                                coe
                                                                                                  (case coe
                                                                                                          v19 of
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                       -> if coe
                                                                                                               v20
                                                                                                            then coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v21)
                                                                                                                   (coe
                                                                                                                      C_success_276
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                         (coe
                                                                                                                            d_size_424
                                                                                                                            (coe
                                                                                                                               v0)))
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                         (coe
                                                                                                                            d_debruijn_428
                                                                                                                            (coe
                                                                                                                               v0))
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                            (coe
                                                                                                                               v12)
                                                                                                                            (coe
                                                                                                                               v13)
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Once.Type.C__'43'__124
                                                                                                                               (coe
                                                                                                                                  v12)
                                                                                                                               (coe
                                                                                                                                  v18)))
                                                                                                                         (coe
                                                                                                                            du_specInl_534))
                                                                                                                      (coe
                                                                                                                         (0 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         d_freshCounter_430
                                                                                                                         (coe
                                                                                                                            v0)))
                                                                                                            else coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v21)
                                                                                                                   (coe
                                                                                                                      C_failure_278
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                         (coe
                                                                                                                            ("inl"
                                                                                                                             ::
                                                                                                                             Data.Text.Text))))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> coe
                                                                                                  v11
                                                                                    _ -> coe v11
                                                                             _ -> coe v11
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'inr_1760
                             -> let v7 = "inr" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_786 (coe ("inr" :: Data.Text.Text))
                                             (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                             (coe d_debruijn_428 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_430 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__176
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_276
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_278
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_626
                                                       (coe d_imports_432 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_424 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_430
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__176
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_276
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_278
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_278 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                 -> case coe v13 of
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> case coe v16 of
                                                                                    MAlonzo.Code.Once.Type.C_pure_34
                                                                                      -> case coe
                                                                                                v14 of
                                                                                           MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                                                                                             -> let v19
                                                                                                      = d__'8799'T__176
                                                                                                          (coe
                                                                                                             v12)
                                                                                                          (coe
                                                                                                             v18) in
                                                                                                coe
                                                                                                  (case coe
                                                                                                          v19 of
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                       -> if coe
                                                                                                               v20
                                                                                                            then coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v21)
                                                                                                                   (coe
                                                                                                                      C_success_276
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                         (coe
                                                                                                                            d_size_424
                                                                                                                            (coe
                                                                                                                               v0)))
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                         (coe
                                                                                                                            d_debruijn_428
                                                                                                                            (coe
                                                                                                                               v0))
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                            (coe
                                                                                                                               v12)
                                                                                                                            (coe
                                                                                                                               v13)
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Once.Type.C__'43'__124
                                                                                                                               (coe
                                                                                                                                  v17)
                                                                                                                               (coe
                                                                                                                                  v12)))
                                                                                                                         (coe
                                                                                                                            du_specInr_544))
                                                                                                                      (coe
                                                                                                                         (0 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         d_freshCounter_430
                                                                                                                         (coe
                                                                                                                            v0)))
                                                                                                            else coe
                                                                                                                   seq
                                                                                                                   (coe
                                                                                                                      v21)
                                                                                                                   (coe
                                                                                                                      C_failure_278
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                         (coe
                                                                                                                            ("inr"
                                                                                                                             ::
                                                                                                                             Data.Text.Text))))
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> coe
                                                                                                  v11
                                                                                    _ -> coe v11
                                                                             _ -> coe v11
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'arr_1762
                             -> let v7 = "arr" :: Data.Text.Text in
                                coe
                                  (let v8
                                         = coe
                                             du_go_786 (coe ("arr" :: Data.Text.Text))
                                             (coe d_size_424 (coe v0)) (coe d_named_426 (coe v0))
                                             (coe d_debruijn_428 (coe v0)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                          -> case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> let v14 = 0 :: Integer in
                                                           coe
                                                             (let v15
                                                                    = d_freshCounter_430 (coe v0) in
                                                              coe
                                                                (let v16
                                                                       = d__'8799'T__176
                                                                           (coe v2) (coe v10) in
                                                                 coe
                                                                   (case coe v16 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                        -> if coe v17
                                                                             then coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_success_276
                                                                                       (coe v12)
                                                                                       (coe v13)
                                                                                       (coe v14)
                                                                                       (coe v15))
                                                                             else coe
                                                                                    seq (coe v18)
                                                                                    (coe
                                                                                       C_failure_278
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                          (coe v2)
                                                                                          (coe
                                                                                             v10)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> let v9
                                                   = d_lookupImport_626
                                                       (coe d_imports_432 (coe v0)) (coe v7) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> let v11
                                                             = MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_424 (coe v0)) in
                                                       coe
                                                         (let v12
                                                                = coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                    v7 in
                                                          coe
                                                            (let v13 = 0 :: Integer in
                                                             coe
                                                               (let v14
                                                                      = d_freshCounter_430
                                                                          (coe v0) in
                                                                coe
                                                                  (let v15
                                                                         = d__'8799'T__176
                                                                             (coe v2) (coe v10) in
                                                                   coe
                                                                     (case coe v15 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                          -> if coe v16
                                                                               then coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_success_276
                                                                                         (coe v11)
                                                                                         (coe v12)
                                                                                         (coe v13)
                                                                                         (coe v14))
                                                                               else coe
                                                                                      seq (coe v17)
                                                                                      (coe
                                                                                         C_failure_278
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v10)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))))
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> let v10
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                 (coe v7) in
                                                       coe
                                                         (let v11 = coe C_failure_278 (coe v10) in
                                                          coe
                                                            (case coe v2 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                                                 -> case coe v12 of
                                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                                                               -> case coe v18 of
                                                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                                                      -> case coe
                                                                                                v19 of
                                                                                           MAlonzo.Code.Once.Type.C_pure_34
                                                                                             -> case coe
                                                                                                       v13 of
                                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v20 v21
                                                                                                    -> case coe
                                                                                                              v20 of
                                                                                                         MAlonzo.Code.Once.Type.C_Many_10
                                                                                                           -> case coe
                                                                                                                     v21 of
                                                                                                                MAlonzo.Code.Once.Type.C_pure_34
                                                                                                                  -> case coe
                                                                                                                            v14 of
                                                                                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v22 v23 v24
                                                                                                                         -> case coe
                                                                                                                                   v23 of
                                                                                                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                                                                                                                                -> case coe
                                                                                                                                          v25 of
                                                                                                                                     MAlonzo.Code.Once.Type.C_Many_10
                                                                                                                                       -> case coe
                                                                                                                                                 v26 of
                                                                                                                                            MAlonzo.Code.Once.Type.C_eff_36
                                                                                                                                              -> let v27
                                                                                                                                                       = d__'8799'T__176
                                                                                                                                                           (coe
                                                                                                                                                              v15)
                                                                                                                                                           (coe
                                                                                                                                                              v22) in
                                                                                                                                                 coe
                                                                                                                                                   (let v28
                                                                                                                                                          = d__'8799'T__176
                                                                                                                                                              (coe
                                                                                                                                                                 v17)
                                                                                                                                                              (coe
                                                                                                                                                                 v24) in
                                                                                                                                                    coe
                                                                                                                                                      (case coe
                                                                                                                                                              v27 of
                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v29 v30
                                                                                                                                                           -> let v31
                                                                                                                                                                    = coe
                                                                                                                                                                        C_failure_278
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                                                                           (coe
                                                                                                                                                                              ("arr"
                                                                                                                                                                               ::
                                                                                                                                                                               Data.Text.Text))) in
                                                                                                                                                              coe
                                                                                                                                                                (case coe
                                                                                                                                                                        v29 of
                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                                                                     -> case coe
                                                                                                                                                                               v30 of
                                                                                                                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v32
                                                                                                                                                                            -> case coe
                                                                                                                                                                                      v28 of
                                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                                                                                                   -> case coe
                                                                                                                                                                                             v33 of
                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                                                                                          -> case coe
                                                                                                                                                                                                    v34 of
                                                                                                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v35
                                                                                                                                                                                                 -> coe
                                                                                                                                                                                                      C_success_276
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            d_size_424
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               v0)))
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            d_debruijn_428
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               v0))
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v15)
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v25)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v21))
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v17))
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v25)
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v21))
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v15)
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v23)
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v17)))
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            du_specArr_620))
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         (0 ::
                                                                                                                                                                                                            Integer))
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         d_freshCounter_430
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            v0))
                                                                                                                                                                                               _ -> coe
                                                                                                                                                                                                      v31
                                                                                                                                                                                        _ -> coe
                                                                                                                                                                                               v31
                                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                          _ -> coe
                                                                                                                                                                                 v31
                                                                                                                                                                   _ -> coe
                                                                                                                                                                          v31)
                                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                            _ -> coe
                                                                                                                                                   v11
                                                                                                                                     _ -> coe
                                                                                                                                            v11
                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                       _ -> coe
                                                                                                                              v11
                                                                                                                _ -> coe
                                                                                                                       v11
                                                                                                         _ -> coe
                                                                                                                v11
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           _ -> coe
                                                                                                  v11
                                                                                    _ -> coe v11
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> coe v11
                                                               _ -> coe v11))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           C_bbc'45'other_1766
                             -> let v8
                                      = coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                          erased
                                          (\ v8 ->
                                             coe
                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                               (coe v1))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                             (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                v1)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                ("unit" :: Data.Text.Text))) in
                                coe
                                  (case coe v8 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                       -> if coe v9
                                            then let v11
                                                       = seq
                                                           (coe v10)
                                                           (coe
                                                              C_success_252
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_Unit_118)
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                 (coe d_size_424 (coe v0)))
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
                                                              (coe (0 :: Integer))
                                                              (coe d_freshCounter_430 (coe v0))) in
                                                 coe
                                                   (case coe v11 of
                                                      C_success_252 v12 v13 v14 v15 v16
                                                        -> let v17
                                                                 = d__'8799'T__176
                                                                     (coe v2) (coe v12) in
                                                           coe
                                                             (case coe v17 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                  -> if coe v18
                                                                       then coe
                                                                              seq (coe v19)
                                                                              (coe
                                                                                 C_success_276
                                                                                 (coe v13) (coe v14)
                                                                                 (coe v15)
                                                                                 (coe v16))
                                                                       else coe
                                                                              seq (coe v19)
                                                                              (coe
                                                                                 C_failure_278
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                    (coe v2)
                                                                                    (coe v12)))
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      C_failure_254 v12
                                                        -> let v13
                                                                 = d_lookupPoly_288
                                                                     (coe d_polys_434 (coe v0))
                                                                     (coe v1) in
                                                           coe
                                                             (case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                  -> coe
                                                                       C_success_276
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                          (coe d_size_424 (coe v0)))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_poly_504
                                                                          v1)
                                                                       (coe (0 :: Integer))
                                                                       (coe
                                                                          d_freshCounter_430
                                                                          (coe v0))
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> coe C_failure_278 (coe v12)
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            else (let v11
                                                        = seq
                                                            (coe v10)
                                                            (let v11
                                                                   = coe
                                                                       du_go_786 (coe v1)
                                                                       (coe d_size_424 (coe v0))
                                                                       (coe d_named_426 (coe v0))
                                                                       (coe
                                                                          d_debruijn_428
                                                                          (coe v0)) in
                                                             coe
                                                               (case coe v11 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                    -> case coe v12 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                           -> case coe v14 of
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                  -> coe
                                                                                       C_success_252
                                                                                       (coe v13)
                                                                                       (coe v15)
                                                                                       (coe v16)
                                                                                       (coe
                                                                                          (0 ::
                                                                                             Integer))
                                                                                       (coe
                                                                                          d_freshCounter_430
                                                                                          (coe v0))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> let v12
                                                                             = d_lookupImport_626
                                                                                 (coe
                                                                                    d_imports_432
                                                                                    (coe v0))
                                                                                 (coe v1) in
                                                                       coe
                                                                         (case coe v12 of
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                              -> coe
                                                                                   C_success_252
                                                                                   (coe v13)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                      (coe
                                                                                         d_size_424
                                                                                         (coe v0)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494
                                                                                      v1)
                                                                                   (coe
                                                                                      (0 ::
                                                                                         Integer))
                                                                                   (coe
                                                                                      d_freshCounter_430
                                                                                      (coe v0))
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                              -> coe
                                                                                   C_failure_254
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                                                                                      (coe v1))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)) in
                                                  coe
                                                    (case coe v11 of
                                                       C_success_252 v12 v13 v14 v15 v16
                                                         -> let v17
                                                                  = d__'8799'T__176
                                                                      (coe v2) (coe v12) in
                                                            coe
                                                              (case coe v17 of
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                   -> if coe v18
                                                                        then coe
                                                                               seq (coe v19)
                                                                               (coe
                                                                                  C_success_276
                                                                                  (coe v13)
                                                                                  (coe v14)
                                                                                  (coe v15)
                                                                                  (coe v16))
                                                                        else coe
                                                                               seq (coe v19)
                                                                               (coe
                                                                                  C_failure_278
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                     (coe v2)
                                                                                     (coe v12)))
                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                       C_failure_254 v12
                                                         -> let v13
                                                                  = d_lookupPoly_288
                                                                      (coe d_polys_434 (coe v0))
                                                                      (coe v1) in
                                                            coe
                                                              (case coe v13 of
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                   -> coe
                                                                        C_success_276
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                           (coe
                                                                              d_size_424 (coe v0)))
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_poly_504
                                                                           v1)
                                                                        (coe (0 :: Integer))
                                                                        (coe
                                                                           d_freshCounter_430
                                                                           (coe v0))
                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                   -> coe C_failure_278 (coe v12)
                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkPair
d_checkPair_1864 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_262
d_checkPair_1864 v0 v1 v2 v3
  = let v4
          = coe
              C_failure_278
              (coe
                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                 (coe ("pair" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v7
                  -> case coe v7 of
                       l | (==) l ("pair" :: Data.Text.Text) ->
                           case coe v3 of
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v8 v9 v10
                               -> case coe v9 of
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v11 v12
                                      -> case coe v11 of
                                           MAlonzo.Code.Once.Type.C_Many_10
                                             -> case coe v12 of
                                                  MAlonzo.Code.Once.Type.C_pure_34
                                                    -> case coe v10 of
                                                         MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                                           -> let v15
                                                                    = d_checkElab_1846
                                                                        (coe v0) (coe v6)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                           (coe v8) (coe v9)
                                                                           (coe v13)) in
                                                              coe
                                                                (case coe v15 of
                                                                   C_success_276 v16 v17 v18 v19
                                                                     -> let v20
                                                                              = d_checkElab_1846
                                                                                  (coe v0) (coe v2)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                     (coe v8)
                                                                                     (coe v9)
                                                                                     (coe v14)) in
                                                                        coe
                                                                          (case coe v20 of
                                                                             C_success_276 v21 v22 v23 v24
                                                                               -> coe
                                                                                    C_success_276
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                             (coe
                                                                                                d_size_424
                                                                                                (coe
                                                                                                   v0)))
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                             (coe
                                                                                                v11)
                                                                                             (coe
                                                                                                v16)))
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                          (coe v11)
                                                                                          (coe
                                                                                             v21)))
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                             (coe
                                                                                                d_size_424
                                                                                                (coe
                                                                                                   v0)))
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                             (coe
                                                                                                v11)
                                                                                             (coe
                                                                                                v16)))
                                                                                       v21
                                                                                       (MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                          (coe v8)
                                                                                          (coe v14))
                                                                                       v11
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                          (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                             (coe
                                                                                                d_size_424
                                                                                                (coe
                                                                                                   v0)))
                                                                                          v16
                                                                                          (MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                             (coe
                                                                                                v8)
                                                                                             (coe
                                                                                                v13))
                                                                                          v11
                                                                                          (coe
                                                                                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                             (coe
                                                                                                d_debruijn_428
                                                                                                (coe
                                                                                                   v0))
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                   (coe
                                                                                                      v8)
                                                                                                   (coe
                                                                                                      v13))
                                                                                                (coe
                                                                                                   v9)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                      (coe
                                                                                                         v8)
                                                                                                      (coe
                                                                                                         v14))
                                                                                                   (coe
                                                                                                      v9)
                                                                                                   (coe
                                                                                                      v3)))
                                                                                             (coe
                                                                                                du_specPair_558
                                                                                                (coe
                                                                                                   v8)))
                                                                                          v17)
                                                                                       v22)
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                          (coe v18)
                                                                                          (coe
                                                                                             v23)))
                                                                                    (coe v24)
                                                                             C_failure_278 v21
                                                                               -> coe v20
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                   C_failure_278 v16 -> coe v15
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> coe v4
                                                  _ -> coe v4
                                           _ -> coe v4
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkCompose
d_checkCompose_1874 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_262
d_checkCompose_1874 v0 v1 v2 v3
  = let v4
          = coe
              C_failure_278
              (coe
                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                 (coe ("compose" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v7
                  -> case coe v7 of
                       l | (==) l ("compose" :: Data.Text.Text) ->
                           case coe v3 of
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v8 v9 v10
                               -> case coe v9 of
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v11 v12
                                      -> case coe v11 of
                                           MAlonzo.Code.Once.Type.C_Many_10
                                             -> case coe v12 of
                                                  MAlonzo.Code.Once.Type.C_pure_34
                                                    -> let v13
                                                             = d_inferElab_1840 (coe v0) (coe v2) in
                                                       coe
                                                         (case coe v13 of
                                                            C_success_252 v14 v15 v16 v17 v18
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Once.Type.C_Unit_118
                                                                     -> coe
                                                                          C_failure_278
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                             (coe
                                                                                ("compose"
                                                                                 ::
                                                                                 Data.Text.Text)))
                                                                   MAlonzo.Code.Once.Type.C_Void_120
                                                                     -> coe
                                                                          C_failure_278
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                             (coe
                                                                                ("compose"
                                                                                 ::
                                                                                 Data.Text.Text)))
                                                                   MAlonzo.Code.Once.Type.C__'42'__122 v19 v20
                                                                     -> coe
                                                                          C_failure_278
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                             (coe
                                                                                ("compose"
                                                                                 ::
                                                                                 Data.Text.Text)))
                                                                   MAlonzo.Code.Once.Type.C__'43'__124 v19 v20
                                                                     -> coe
                                                                          C_failure_278
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                             (coe
                                                                                ("compose"
                                                                                 ::
                                                                                 Data.Text.Text)))
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v19 v20 v21
                                                                     -> case coe v20 of
                                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                                                                            -> case coe v22 of
                                                                                 MAlonzo.Code.Once.Type.C_Zero_6
                                                                                   -> coe
                                                                                        seq
                                                                                        (coe v23)
                                                                                        (coe
                                                                                           C_failure_278
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                              (coe
                                                                                                 ("compose"
                                                                                                  ::
                                                                                                  Data.Text.Text))))
                                                                                 MAlonzo.Code.Once.Type.C_One_8
                                                                                   -> coe
                                                                                        seq
                                                                                        (coe v23)
                                                                                        (coe
                                                                                           C_failure_278
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                              (coe
                                                                                                 ("compose"
                                                                                                  ::
                                                                                                  Data.Text.Text))))
                                                                                 MAlonzo.Code.Once.Type.C_Many_10
                                                                                   -> case coe
                                                                                             v23 of
                                                                                        MAlonzo.Code.Once.Type.C_pure_34
                                                                                          -> let v24
                                                                                                   = d__'8799'T__176
                                                                                                       (coe
                                                                                                          v8)
                                                                                                       (coe
                                                                                                          v19) in
                                                                                             coe
                                                                                               (case coe
                                                                                                       v24 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                                                    -> if coe
                                                                                                            v25
                                                                                                         then coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v26)
                                                                                                                (let v27
                                                                                                                       = d_checkElab_1846
                                                                                                                           (coe
                                                                                                                              v0)
                                                                                                                           (coe
                                                                                                                              v6)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                              (coe
                                                                                                                                 v21)
                                                                                                                              (coe
                                                                                                                                 v20)
                                                                                                                              (coe
                                                                                                                                 v10)) in
                                                                                                                 coe
                                                                                                                   (case coe
                                                                                                                           v27 of
                                                                                                                      C_success_276 v28 v29 v30 v31
                                                                                                                        -> coe
                                                                                                                             C_success_276
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                                      (coe
                                                                                                                                         d_size_424
                                                                                                                                         (coe
                                                                                                                                            v0)))
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                                                                      (coe
                                                                                                                                         v22)
                                                                                                                                      (coe
                                                                                                                                         v28)))
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                                                                   (coe
                                                                                                                                      v22)
                                                                                                                                   (coe
                                                                                                                                      v15)))
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                                      (coe
                                                                                                                                         d_size_424
                                                                                                                                         (coe
                                                                                                                                            v0)))
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                                                                      (coe
                                                                                                                                         v22)
                                                                                                                                      (coe
                                                                                                                                         v28)))
                                                                                                                                v15
                                                                                                                                (MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                                                   (coe
                                                                                                                                      v19)
                                                                                                                                   (coe
                                                                                                                                      v21))
                                                                                                                                v22
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                                                                   (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                                                      (coe
                                                                                                                                         d_size_424
                                                                                                                                         (coe
                                                                                                                                            v0)))
                                                                                                                                   v28
                                                                                                                                   (MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                                                      (coe
                                                                                                                                         v21)
                                                                                                                                      (coe
                                                                                                                                         v10))
                                                                                                                                   v22
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                                                      (coe
                                                                                                                                         d_debruijn_428
                                                                                                                                         (coe
                                                                                                                                            v0))
                                                                                                                                      (coe
                                                                                                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                                         (coe
                                                                                                                                            MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                                                            (coe
                                                                                                                                               v21)
                                                                                                                                            (coe
                                                                                                                                               v10))
                                                                                                                                         (coe
                                                                                                                                            v20)
                                                                                                                                         (coe
                                                                                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                                                               (coe
                                                                                                                                                  v19)
                                                                                                                                               (coe
                                                                                                                                                  v21))
                                                                                                                                            (coe
                                                                                                                                               v20)
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                                               (coe
                                                                                                                                                  v19)
                                                                                                                                               (coe
                                                                                                                                                  v20)
                                                                                                                                               (coe
                                                                                                                                                  v10))))
                                                                                                                                      (coe
                                                                                                                                         du_specCompose_608
                                                                                                                                         (coe
                                                                                                                                            v19)
                                                                                                                                         (coe
                                                                                                                                            v21)))
                                                                                                                                   v29)
                                                                                                                                v16)
                                                                                                                             (coe
                                                                                                                                addInt
                                                                                                                                (coe
                                                                                                                                   (1 ::
                                                                                                                                      Integer))
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                   (coe
                                                                                                                                      v30)
                                                                                                                                   (coe
                                                                                                                                      v17)))
                                                                                                                             (coe
                                                                                                                                v31)
                                                                                                                      C_failure_278 v28
                                                                                                                        -> coe
                                                                                                                             v27
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                         else coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v26)
                                                                                                                (coe
                                                                                                                   C_failure_278
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                                      (coe
                                                                                                                         ("compose"
                                                                                                                          ::
                                                                                                                          Data.Text.Text))))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                        MAlonzo.Code.Once.Type.C_eff_36
                                                                                          -> coe
                                                                                               C_failure_278
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                                  (coe
                                                                                                     ("compose"
                                                                                                      ::
                                                                                                      Data.Text.Text)))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Once.Type.C_μ'45'type_128 v19
                                                                     -> coe
                                                                          C_failure_278
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                             (coe
                                                                                ("compose"
                                                                                 ::
                                                                                 Data.Text.Text)))
                                                                   MAlonzo.Code.Once.Type.C_ν'45'type_130 v19
                                                                     -> coe
                                                                          C_failure_278
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                             (coe
                                                                                ("compose"
                                                                                 ::
                                                                                 Data.Text.Text)))
                                                                   MAlonzo.Code.Once.Type.C_Int_132
                                                                     -> coe
                                                                          C_failure_278
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                             (coe
                                                                                ("compose"
                                                                                 ::
                                                                                 Data.Text.Text)))
                                                                   MAlonzo.Code.Once.Type.C_Float_134
                                                                     -> coe
                                                                          C_failure_278
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                             (coe
                                                                                ("compose"
                                                                                 ::
                                                                                 Data.Text.Text)))
                                                                   MAlonzo.Code.Once.Type.C_Str_136
                                                                     -> coe
                                                                          C_failure_278
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                             (coe
                                                                                ("compose"
                                                                                 ::
                                                                                 Data.Text.Text)))
                                                                   MAlonzo.Code.Once.Type.C_Buffer_138
                                                                     -> coe
                                                                          C_failure_278
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                             (coe
                                                                                ("compose"
                                                                                 ::
                                                                                 Data.Text.Text)))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            C_failure_254 v14
                                                              -> let v15
                                                                       = d_composeArgB_1650
                                                                           (coe v0) (coe v2)
                                                                           (coe v8) in
                                                                 coe
                                                                   (case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                        -> let v17
                                                                                 = d_checkElab_1846
                                                                                     (coe v0)
                                                                                     (coe v2)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                        (coe v8)
                                                                                        (coe v9)
                                                                                        (coe
                                                                                           v16)) in
                                                                           coe
                                                                             (case coe v17 of
                                                                                C_success_276 v18 v19 v20 v21
                                                                                  -> let v22
                                                                                           = d_checkElab_1846
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  v6)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                  (coe
                                                                                                     v16)
                                                                                                  (coe
                                                                                                     v9)
                                                                                                  (coe
                                                                                                     v10)) in
                                                                                     coe
                                                                                       (case coe
                                                                                               v22 of
                                                                                          C_success_276 v23 v24 v25 v26
                                                                                            -> coe
                                                                                                 C_success_276
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                          (coe
                                                                                                             d_size_424
                                                                                                             (coe
                                                                                                                v0)))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                                          (coe
                                                                                                             v11)
                                                                                                          (coe
                                                                                                             v23)))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                                       (coe
                                                                                                          v11)
                                                                                                       (coe
                                                                                                          v18)))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                          (coe
                                                                                                             d_size_424
                                                                                                             (coe
                                                                                                                v0)))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                                          (coe
                                                                                                             v11)
                                                                                                          (coe
                                                                                                             v23)))
                                                                                                    v18
                                                                                                    (MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                       (coe
                                                                                                          v8)
                                                                                                       (coe
                                                                                                          v16))
                                                                                                    v11
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                                       (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                                          (coe
                                                                                                             d_size_424
                                                                                                             (coe
                                                                                                                v0)))
                                                                                                       v23
                                                                                                       (MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                          (coe
                                                                                                             v16)
                                                                                                          (coe
                                                                                                             v10))
                                                                                                       v11
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                                          (coe
                                                                                                             d_debruijn_428
                                                                                                             (coe
                                                                                                                v0))
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                                (coe
                                                                                                                   v16)
                                                                                                                (coe
                                                                                                                   v10))
                                                                                                             (coe
                                                                                                                v9)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                                                   (coe
                                                                                                                      v8)
                                                                                                                   (coe
                                                                                                                      v16))
                                                                                                                (coe
                                                                                                                   v9)
                                                                                                                (coe
                                                                                                                   v3)))
                                                                                                          (coe
                                                                                                             du_specCompose_608
                                                                                                             (coe
                                                                                                                v8)
                                                                                                             (coe
                                                                                                                v16)))
                                                                                                       v24)
                                                                                                    v19)
                                                                                                 (coe
                                                                                                    addInt
                                                                                                    (coe
                                                                                                       (1 ::
                                                                                                          Integer))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                       (coe
                                                                                                          v25)
                                                                                                       (coe
                                                                                                          v20)))
                                                                                                 (coe
                                                                                                    v26)
                                                                                          C_failure_278 v23
                                                                                            -> coe
                                                                                                 v22
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                C_failure_278 v18
                                                                                  -> coe v17
                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                        -> coe
                                                                             C_failure_278
                                                                             (coe
                                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                (coe
                                                                                   ("compose"
                                                                                    ::
                                                                                    Data.Text.Text)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> coe v4
                                           _ -> coe v4
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkCurry
d_checkCurry_1882 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_262
d_checkCurry_1882 v0 v1 v2
  = let v3
          = coe
              C_failure_278
              (coe
                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                 (coe ("curry" :: Data.Text.Text))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v8 of
                              MAlonzo.Code.Once.Type.C_pure_34
                                -> case coe v6 of
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
                                       -> case coe v10 of
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v12 v13
                                              -> case coe v12 of
                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                     -> case coe v13 of
                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                            -> let v14
                                                                     = d_checkElab_1846
                                                                         (coe v0) (coe v1)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C__'42'__122
                                                                               (coe v4) (coe v9))
                                                                            (coe v10) (coe v11)) in
                                                               coe
                                                                 (case coe v14 of
                                                                    C_success_276 v15 v16 v17 v18
                                                                      -> coe
                                                                           C_success_276
                                                                           (coe
                                                                              MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                 (coe
                                                                                    d_size_424
                                                                                    (coe v0)))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                 (coe v12)
                                                                                 (coe v15)))
                                                                           (coe
                                                                              MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                              (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                 (coe
                                                                                    d_size_424
                                                                                    (coe v0)))
                                                                              v15
                                                                              (MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Type.C__'42'__122
                                                                                    (coe v4)
                                                                                    (coe v9))
                                                                                 (coe v11))
                                                                              v12
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                 (coe
                                                                                    d_debruijn_428
                                                                                    (coe v0))
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Type.C__'42'__122
                                                                                          (coe v4)
                                                                                          (coe v9))
                                                                                       (coe v11))
                                                                                    (coe v10)
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                       (coe v4)
                                                                                       (coe v10)
                                                                                       (coe v6)))
                                                                                 (coe
                                                                                    du_specCurry_584
                                                                                    (coe v4)
                                                                                    (coe v9)))
                                                                              v16)
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v17))
                                                                           (coe v18)
                                                                    C_failure_278 v15 -> coe v14
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> coe v3
                                                   _ -> coe v3
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v3
                              _ -> coe v3
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkApply
d_checkApply_1890 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_262
d_checkApply_1890 v0 v1 v2
  = let v3 = d_inferElab_1840 (coe v0) (coe v1) in
    coe
      (case coe v3 of
         C_success_252 v4 v5 v6 v7 v8
           -> case coe v4 of
                MAlonzo.Code.Once.Type.C__'42'__122 v9 v10
                  -> case coe v9 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.Once.Type.C_Many_10
                                       -> case coe v15 of
                                            MAlonzo.Code.Once.Type.C_pure_34
                                              -> let v16 = d__'8799'T__176 (coe v11) (coe v10) in
                                                 coe
                                                   (case coe v16 of
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                        -> if coe v17
                                                             then let v19
                                                                        = seq
                                                                            (coe v18)
                                                                            (coe
                                                                               C_success_252
                                                                               (coe v13)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                     (coe
                                                                                        d_size_424
                                                                                        (coe v0)))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                                                                     (coe v14)
                                                                                     (coe v5)))
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                                                  (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                                                     (coe
                                                                                        d_size_424
                                                                                        (coe v0)))
                                                                                  v5
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C__'42'__122
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                        (coe v11)
                                                                                        (coe v13))
                                                                                     (coe v11))
                                                                                  v14
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                                                     (coe
                                                                                        d_debruijn_428
                                                                                        (coe v0))
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Type.C__'42'__122
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Type.d__'8658'__146
                                                                                              (coe
                                                                                                 v11)
                                                                                              (coe
                                                                                                 v13))
                                                                                           (coe
                                                                                              v11))
                                                                                        (coe v12)
                                                                                        (coe v13))
                                                                                     (coe
                                                                                        d_specApply_596
                                                                                        (coe v11)
                                                                                        (coe v13)))
                                                                                  v6)
                                                                               (coe
                                                                                  addInt
                                                                                  (coe
                                                                                     (1 :: Integer))
                                                                                  (coe v7))
                                                                               (coe v8)) in
                                                                  coe
                                                                    (case coe v19 of
                                                                       C_success_252 v20 v21 v22 v23 v24
                                                                         -> let v25
                                                                                  = d__'8799'T__176
                                                                                      (coe v2)
                                                                                      (coe v20) in
                                                                            coe
                                                                              (case coe v25 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                   -> if coe v26
                                                                                        then coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v27)
                                                                                               (coe
                                                                                                  C_success_276
                                                                                                  (coe
                                                                                                     v21)
                                                                                                  (coe
                                                                                                     v22)
                                                                                                  (coe
                                                                                                     v23)
                                                                                                  (coe
                                                                                                     v24))
                                                                                        else coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v27)
                                                                                               (coe
                                                                                                  C_failure_278
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                                     (coe
                                                                                                        v2)
                                                                                                     (coe
                                                                                                        v20)))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       C_failure_254 v20
                                                                         -> coe
                                                                              C_failure_278
                                                                              (coe v20)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                             else (let v19
                                                                         = seq
                                                                             (coe v18)
                                                                             (coe
                                                                                C_failure_254
                                                                                (coe
                                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                                                   (coe
                                                                                      ("apply"
                                                                                       ::
                                                                                       Data.Text.Text)))) in
                                                                   coe
                                                                     (case coe v19 of
                                                                        C_success_252 v20 v21 v22 v23 v24
                                                                          -> let v25
                                                                                   = d__'8799'T__176
                                                                                       (coe v2)
                                                                                       (coe v20) in
                                                                             coe
                                                                               (case coe v25 of
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                    -> if coe v26
                                                                                         then coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v27)
                                                                                                (coe
                                                                                                   C_success_276
                                                                                                   (coe
                                                                                                      v21)
                                                                                                   (coe
                                                                                                      v22)
                                                                                                   (coe
                                                                                                      v23)
                                                                                                   (coe
                                                                                                      v24))
                                                                                         else coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v27)
                                                                                                (coe
                                                                                                   C_failure_278
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                                                                                      (coe
                                                                                                         v2)
                                                                                                      (coe
                                                                                                         v20)))
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                        C_failure_254 v20
                                                                          -> coe
                                                                               C_failure_278
                                                                               (coe v20)
                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> let v16
                                                       = coe
                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                           (coe ("apply" :: Data.Text.Text)) in
                                                 coe (coe C_failure_278 (coe v16))
                                     _ -> let v16
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe (coe C_failure_278 (coe v16))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> let v11
                                  = coe
                                      MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                                      (coe ("apply" :: Data.Text.Text)) in
                            coe (coe C_failure_278 (coe v11))
                _ -> let v9
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_68
                               (coe ("apply" :: Data.Text.Text)) in
                     coe (coe C_failure_278 (coe v9))
         C_failure_254 v4
           -> case coe v3 of
                C_success_252 v5 v6 v7 v8 v9
                  -> let v10 = d__'8799'T__176 (coe v2) (coe v5) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                            -> if coe v11
                                 then coe
                                        seq (coe v12)
                                        (coe C_success_276 (coe v6) (coe v7) (coe v8) (coe v9))
                                 else coe
                                        seq (coe v12)
                                        (coe
                                           C_failure_278
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_52
                                              (coe v2) (coe v5)))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_254 v5 -> coe C_failure_278 (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate._.mkArith
d_mkArith_3040 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_mkArith_3040 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               ~v12 v13 v14 v15
  = du_mkArith_3040 v13 v14 v15
du_mkArith_3040 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_mkArith_3040 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_add_366 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_sub_376 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_mul_386 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_div_396 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_406 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_add_366 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_add_366 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_add_366 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_add_366 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_add_366 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_add_366 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._.mkCmp
d_mkCmp_3048 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_mkCmp_3048 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             v13 v14 v15
  = du_mkCmp_3048 v13 v14 v15
du_mkCmp_3048 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_mkCmp_3048 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lt_424 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lt_424 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lt_424 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lt_424 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lt_424 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_lt_424 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_le_434 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_gt_444 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_ge_454 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_eq_464 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_ne_474 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElab-fallback-RInt
d_checkElab'45'fallback'45'RInt_5494 ::
  T_NamedCtx_410 -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RInt_5494 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_int_350 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_430 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RStringLit
d_checkElab'45'fallback'45'RStringLit_5524 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RStringLit_5524 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_str_356 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_430 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RUnit
d_checkElab'45'fallback'45'RUnit_5552 ::
  T_NamedCtx_410 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnit_5552 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_430 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RQualified
d_checkElab'45'fallback'45'RQualified_5588 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RQualified_5588 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
                                           v7 ~v8
  = du_checkElab'45'fallback'45'RQualified_5588 v3 v5 v6 v7
du_checkElab'45'fallback'45'RQualified_5588 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RQualified_5588 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RAnnot
d_checkElab'45'fallback'45'RAnnot_5644 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RAnnot_5644 ~v0 ~v1 v2 ~v3 v4 v5 v6 ~v7
  = du_checkElab'45'fallback'45'RAnnot_5644 v2 v4 v5 v6
du_checkElab'45'fallback'45'RAnnot_5644 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RAnnot_5644 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RPair
d_checkElab'45'fallback'45'RPair_5696 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RPair_5696 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
                                      ~v8
  = du_checkElab'45'fallback'45'RPair_5696 v3 v5 v6 v7
du_checkElab'45'fallback'45'RPair_5696 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RPair_5696 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RLet
d_checkElab'45'fallback'45'RLet_5756 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RLet_5756 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7
                                     v8 ~v9
  = du_checkElab'45'fallback'45'RLet_5756 v4 v6 v7 v8
du_checkElab'45'fallback'45'RLet_5756 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RLet_5756 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RDestruct
d_checkElab'45'fallback'45'RDestruct_5826 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RDestruct_5826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                          v6 ~v7 v8 v9 v10 ~v11
  = du_checkElab'45'fallback'45'RDestruct_5826 v6 v8 v9 v10
du_checkElab'45'fallback'45'RDestruct_5826 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RDestruct_5826 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RUnaryOp
d_checkElab'45'fallback'45'RUnaryOp_5902 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_UnaryOp_30 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RUnaryOp_5902 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
                                         v7 ~v8
  = du_checkElab'45'fallback'45'RUnaryOp_5902 v3 v5 v6 v7
du_checkElab'45'fallback'45'RUnaryOp_5902 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RUnaryOp_5902 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-unit
d_checkElab'45'fallback'45'RVar'45'unit_5946 ::
  T_NamedCtx_410 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'unit_5946 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_430 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-id
d_checkElab'45'fallback'45'RVar'45'id_5970 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'id_5970 v0 v1 ~v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'id_5970 v0 v1
du_checkElab'45'fallback'45'RVar'45'id_5970 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'id_5970 v0 v1
  = let v2 = d__'8799'T__176 (coe v1) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                             (coe d_debruijn_428 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                                   (coe MAlonzo.Code.Once.Type.C_pure_34))
                                (coe v1))
                             (coe du_specId_506))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe d_freshCounter_430 (coe v0)) erased)))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-fst
d_checkElab'45'fallback'45'RVar'45'fst_6022 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'fst_6022 v0 v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'fst_6022 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'fst_6022 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'fst_6022 v0 v1 v2
  = let v3 = d__'8799'T__176 (coe v1) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                             (coe d_debruijn_428 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v1) (coe v2))
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                                   (coe MAlonzo.Code.Once.Type.C_pure_34))
                                (coe v1))
                             (coe du_specFst_514 (coe v2)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe d_freshCounter_430 (coe v0)) erased)))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-snd
d_checkElab'45'fallback'45'RVar'45'snd_6080 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'snd_6080 v0 v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'snd_6080 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'snd_6080 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'snd_6080 v0 v1 v2
  = let v3 = d__'8799'T__176 (coe v2) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                             (coe d_debruijn_428 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v1) (coe v2))
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                                   (coe MAlonzo.Code.Once.Type.C_pure_34))
                                (coe v2))
                             (coe du_specSnd_524 (coe v1)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe d_freshCounter_430 (coe v0)) erased)))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-terminal
d_checkElab'45'fallback'45'RVar'45'terminal_6136 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'terminal_6136 v0 v1 ~v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'terminal_6136 v0 v1
du_checkElab'45'fallback'45'RVar'45'terminal_6136 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'terminal_6136 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
         (coe d_debruijn_428 (coe v0))
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
            (coe
               MAlonzo.Code.Once.Type.C_mk'45'kind_50
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_pure_34))
            (coe MAlonzo.Code.Once.Type.C_Unit_118))
         (coe du_specTerminal_568))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_430 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-initial
d_checkElab'45'fallback'45'RVar'45'initial_6164 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'initial_6164 v0 v1 ~v2 ~v3
  = du_checkElab'45'fallback'45'RVar'45'initial_6164 v0 v1
du_checkElab'45'fallback'45'RVar'45'initial_6164 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'initial_6164 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
         (coe d_debruijn_428 (coe v0))
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
            (coe MAlonzo.Code.Once.Type.C_Void_120)
            (coe
               MAlonzo.Code.Once.Type.C_mk'45'kind_50
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_pure_34))
            (coe v1))
         (coe du_specInitial_574))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe d_freshCounter_430 (coe v0)) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-inl
d_checkElab'45'fallback'45'RVar'45'inl_6194 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inl_6194 v0 v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'inl_6194 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'inl_6194 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inl_6194 v0 v1 v2
  = let v3 = d__'8799'T__176 (coe v1) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                             (coe d_debruijn_428 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                                   (coe MAlonzo.Code.Once.Type.C_pure_34))
                                (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v1) (coe v2)))
                             (coe du_specInl_534))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe d_freshCounter_430 (coe v0)) erased)))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-inr
d_checkElab'45'fallback'45'RVar'45'inr_6252 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'inr_6252 v0 v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'inr_6252 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'inr_6252 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'inr_6252 v0 v1 v2
  = let v3 = d__'8799'T__176 (coe v2) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                             (coe d_debruijn_428 (coe v0))
                             (coe
                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v2)
                                (coe
                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                                   (coe MAlonzo.Code.Once.Type.C_pure_34))
                                (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v1) (coe v2)))
                             (coe du_specInr_544))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe d_freshCounter_430 (coe v0)) erased)))
                else coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-arr
d_checkElab'45'fallback'45'RVar'45'arr_6310 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'arr_6310 v0 v1 v2 ~v3 ~v4
  = du_checkElab'45'fallback'45'RVar'45'arr_6310 v0 v1 v2
du_checkElab'45'fallback'45'RVar'45'arr_6310 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'arr_6310 v0 v1 v2
  = let v3 = d__'8799'T__176 (coe v1) (coe v1) in
    coe
      (let v4 = d__'8799'T__176 (coe v2) (coe v2) in
       coe
         (let v5
                = case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                      -> coe
                           seq (coe v5)
                           (coe
                              seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                    _ -> MAlonzo.RTE.mazUnreachableError in
          coe
            (case coe v3 of
               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                 -> let v8
                          = case coe v4 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                -> case coe v8 of
                                     MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                       -> case coe v9 of
                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                              -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError in
                    coe
                      (if coe v6
                         then case coe v7 of
                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v9
                                  -> case coe v4 of
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                         -> case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                -> case coe v11 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                       -> coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                               (coe d_debruijn_428 (coe v0))
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                     (coe v1)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_pure_34))
                                                                     (coe v2))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_Many_10)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_pure_34))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                     (coe v1)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_eff_36))
                                                                     (coe v2)))
                                                               (coe du_specArr_620))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe (0 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe d_freshCounter_430 (coe v0))
                                                                  erased))
                                                     _ -> coe v8
                                              _ -> coe v8
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> coe v8
                         else (case coe v7 of
                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                   -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                 _ -> coe v8))
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-pair
d_checkElab'45'fallback'45'RApp'45'pair_6402 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'pair_6402 v0 ~v1 ~v2 v3 v4 v5 v6
                                             v7 v8 v9 v10 ~v11 v12 v13 ~v14 ~v15
  = du_checkElab'45'fallback'45'RApp'45'pair_6402
      v0 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13
du_checkElab'45'fallback'45'RApp'45'pair_6402 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'pair_6402 v0 v1 v2 v3 v4 v5 v6
                                              v7 v8 v9 v10
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_app_214
         (coe
            MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
            (coe
               MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
               (coe d_size_424 (coe v0)))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4)))
         v5 (MAlonzo.Code.Once.Type.d__'8658'__146 (coe v1) (coe v3))
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_app_214
            (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
               (coe d_size_424 (coe v0)))
            v4 (MAlonzo.Code.Once.Type.d__'8658'__146 (coe v1) (coe v2))
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe
               MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
               (coe d_debruijn_428 (coe v0))
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                  (coe MAlonzo.Code.Once.Type.d__'8658'__146 (coe v1) (coe v2))
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                  (coe
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                     (coe MAlonzo.Code.Once.Type.d__'8658'__146 (coe v1) (coe v3))
                     (coe
                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_pure_34))
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
                        (coe
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_pure_34))
                        (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v3)))))
               (coe du_specPair_558 (coe v1)))
            v6)
         v7)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            addInt (coe (1 :: Integer))
            (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v9)))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-compose
d_checkElab'45'fallback'45'RApp'45'compose_6462 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'compose_6462 v0 ~v1 ~v2 v3 v4 v5
                                                v6 v7 v8 v9 v10 v11 v12 ~v13 ~v14 ~v15
  = du_checkElab'45'fallback'45'RApp'45'compose_6462
      v0 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_checkElab'45'fallback'45'RApp'45'compose_6462 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'compose_6462 v0 v1 v2 v3 v4 v5
                                                 v6 v7 v8 v9 v10
  = let v11 = d__'8799'T__176 (coe v1) (coe v1) in
    coe
      (case coe v11 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
           -> if coe v12
                then coe
                       seq (coe v13)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_app_214
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.du__'43''7512'__80
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                   (coe d_size_424 (coe v0)))
                                (coe
                                   MAlonzo.Code.Once.Surface.Syntax.du__'42''7512'__92
                                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4)))
                             v5 (MAlonzo.Code.Once.Type.d__'8658'__146 (coe v1) (coe v2))
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                   (coe d_size_424 (coe v0)))
                                v4 (MAlonzo.Code.Once.Type.d__'8658'__146 (coe v2) (coe v3))
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe
                                   MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                   (coe d_debruijn_428 (coe v0))
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                      (coe MAlonzo.Code.Once.Type.d__'8658'__146 (coe v2) (coe v3))
                                      (coe
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                         (coe
                                            MAlonzo.Code.Once.Type.d__'8658'__146 (coe v1) (coe v2))
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                            (coe MAlonzo.Code.Once.Type.C_pure_34))
                                         (coe
                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
                                            (coe
                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                               (coe MAlonzo.Code.Once.Type.C_Many_10)
                                               (coe MAlonzo.Code.Once.Type.C_pure_34))
                                            (coe v3))))
                                   (coe du_specCompose_608 (coe v1) (coe v2)))
                                v6)
                             v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                addInt (coe (1 :: Integer))
                                (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v10)))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased)))
                else coe
                       seq (coe v13) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-curry
d_checkElab'45'fallback'45'RApp'45'curry_6550 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'curry_6550 v0 ~v1 v2 v3 v4 v5 v6
                                              v7 v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'curry_6550
      v0 v2 v3 v4 v5 v6 v7 v8
du_checkElab'45'fallback'45'RApp'45'curry_6550 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'curry_6550 v0 v1 v2 v3 v4 v5 v6
                                               v7
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_app_214
         (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
            (coe d_size_424 (coe v0)))
         v4
         (MAlonzo.Code.Once.Type.d__'8658'__146
            (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v1) (coe v2))
            (coe v3))
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe
            MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
            (coe d_debruijn_428 (coe v0))
            (coe
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
               (coe
                  MAlonzo.Code.Once.Type.d__'8658'__146
                  (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v1) (coe v2))
                  (coe v3))
               (coe
                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_pure_34))
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                  (coe
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v2)
                     (coe
                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_pure_34))
                     (coe v3))))
            (coe du_specCurry_584 (coe v1) (coe v2)))
         v5)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe addInt (coe (1 :: Integer)) (coe v6))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) erased))
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-apply
d_checkElab'45'fallback'45'RApp'45'apply_6590 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'apply_6590 v0 ~v1 v2 v3 v4 v5 v6
                                              v7 ~v8
  = du_checkElab'45'fallback'45'RApp'45'apply_6590
      v0 v2 v3 v4 v5 v6 v7
du_checkElab'45'fallback'45'RApp'45'apply_6590 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'apply_6590 v0 v1 v2 v3 v4 v5 v6
  = let v7 = d__'8799'T__176 (coe v1) (coe v1) in
    coe
      (case coe v7 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
           -> if coe v8
                then coe
                       seq (coe v9)
                       (let v10 = d__'8799'T__176 (coe v2) (coe v2) in
                        coe
                          (case coe v10 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                               -> if coe v11
                                    then coe
                                           seq (coe v12)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                 (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_60
                                                    (coe d_size_424 (coe v0)))
                                                 v3
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'42'__122
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v1)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                       (coe v2))
                                                    (coe v1))
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094
                                                    (coe d_debruijn_428 (coe v0))
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C__'42'__122
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                             (coe v1)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_pure_34))
                                                             (coe v2))
                                                          (coe v1))
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                       (coe v2))
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_lam_198
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe
                                                          MAlonzo.Code.Once.Surface.Syntax.C_app_214
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                                                             (coe MAlonzo.Code.Once.Type.C_One_8)
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                                                             (coe MAlonzo.Code.Once.Type.C_One_8)
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_'91''93'_52))
                                                          v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fst''_254
                                                             v1
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_var_182
                                                                (coe
                                                                   MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_snd''_266
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                (coe v1)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_Many_10)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_pure_34))
                                                                (coe v2))
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_var_182
                                                                (coe
                                                                   MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
                                                 v4)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe addInt (coe (1 :: Integer)) (coe v5))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe v6) erased)))
                                    else coe
                                           seq (coe v12)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                else coe
                       seq (coe v9) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.resolveExprWF
d_resolveExprWF_6668 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_resolveExprWF_6668 v0 v1 ~v2 v3 v4 ~v5 v6 v7 v8
  = du_resolveExprWF_6668 v0 v1 v3 v4 v6 v7 v8
du_resolveExprWF_6668 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_resolveExprWF_6668 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_182 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_var_182 v9
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198 v10 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_lam_198 v10
                    (coe
                       du_resolveExprWF_6668 (coe addInt (coe (1 :: Integer)) (coe v0))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v16))
                       (coe v18) (coe v3) (coe v4) (coe v5) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_214 v9 v10 v11 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_app_214 v9 v10 v11 v13
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v11)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v13)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v2))
                (coe v3) (coe v4) (coe v5) (coe v14))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1) (coe v11) (coe v3) (coe v4)
                (coe v5) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_228 v9 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_effApp_228 v9 v10 v11
                    (coe
                       du_resolveExprWF_6668 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_eff_36))
                          (coe v17))
                       (coe v3) (coe v4) (coe v5) (coe v13))
                    (coe
                       du_resolveExprWF_6668 (coe v0) (coe v1) (coe v11) (coe v3) (coe v4)
                       (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_242 v9 v10 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__122 v15 v16
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_pair_242 v9 v10
                    (coe
                       du_resolveExprWF_6668 (coe v0) (coe v1) (coe v15) (coe v3) (coe v4)
                       (coe v5) (coe v13))
                    (coe
                       du_resolveExprWF_6668 (coe v0) (coe v1) (coe v16) (coe v3) (coe v4)
                       (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v11
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v11))
                (coe v3) (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v10 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v10) (coe v2))
                (coe v3) (coe v4) (coe v5) (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_278 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inl''_278
                    (coe
                       du_resolveExprWF_6668 (coe v0) (coe v1) (coe v13) (coe v3) (coe v4)
                       (coe v5) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_290 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_inr''_290
                    (coe
                       du_resolveExprWF_6668 (coe v0) (coe v1) (coe v14) (coe v3) (coe v4)
                       (coe v5) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_312 v9 v10 v11 v12 v13 v14 v15 v17 v18 v19
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_case''_312 v9 v10 v11 v12 v13
             v14 v15
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v14) (coe v15))
                (coe v3) (coe v4) (coe v5) (coe v17))
             (coe
                du_resolveExprWF_6668 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v14))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v18))
             (coe
                du_resolveExprWF_6668 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v15))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v19))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_318
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_unit_318
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_328 v11
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_absurd_328
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v3) (coe v4) (coe v5)
                (coe v11))
      MAlonzo.Code.Once.Surface.Syntax.C_let''_344 v9 v10 v11 v12 v14 v15
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_let''_344 v9 v10 v11 v12
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1) (coe v12) (coe v3) (coe v4)
                (coe v5) (coe v14))
             (coe
                du_resolveExprWF_6668 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v1) (coe v12))
                (coe v2) (coe v3) (coe v4) (coe v5) (coe v15))
      MAlonzo.Code.Once.Surface.Syntax.C_int_350 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_int_350 v9
      MAlonzo.Code.Once.Surface.Syntax.C_str_356 v9
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_str_356 v9
      MAlonzo.Code.Once.Surface.Syntax.C_add_366 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_add_366 v9 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v11))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_376 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_sub_376 v9 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v11))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_386 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mul_386 v9 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v11))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_div_396 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_div_396 v9 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v11))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_406 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_mod''_406 v9 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v11))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_414 v10
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_neg_414
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v10))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_424 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_lt_424 v9 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v11))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_le_434 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_le_434 v9 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v11))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_444 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_gt_444 v9 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v11))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_454 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ge_454 v9 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v11))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_464 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_eq_464 v9 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v11))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_474 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Surface.Syntax.C_ne_474 v9 v10
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v11))
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v5)
                (coe v12))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_486 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.Surface.Syntax.C_arr''_486
                    (coe
                       du_resolveExprWF_6668 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.Type.d__'8658'__146 (coe v13) (coe v15))
                       (coe v3) (coe v4) (coe v5) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494 v10
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494 v10
      MAlonzo.Code.Once.Surface.Syntax.C_poly_504 v9
        -> coe
             du_resolvePolyCase_6682 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe v5) (coe v9) (coe v2) (coe d_lookupPoly_288 (coe v3) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.resolvePolyCase
d_resolvePolyCase_6682 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_resolvePolyCase_6682 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 ~v9
  = du_resolvePolyCase_6682 v0 v1 v2 v4 v5 v6 v7 v8
du_resolvePolyCase_6682 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_resolvePolyCase_6682 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v8 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> coe
                    du_applySplice_6698 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                    (coe v5) (coe v6)
                    (coe
                       d_checkElab_1846
                       (coe
                          d_ctxWithImportsAndPolys_444 (coe v3)
                          (coe d_removePoly_324 (coe v5) (coe v2)))
                       (coe v10) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_504 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.applySplice
d_applySplice_6698 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_238 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_262 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_applySplice_6698 v0 v1 v2 ~v3 v4 v5 v6 v7 ~v8 ~v9 ~v10 v11
  = du_applySplice_6698 v0 v1 v2 v4 v5 v6 v7 v11
du_applySplice_6698 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_CheckElabResult_262 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_applySplice_6698 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      C_success_276 v8 v9 v10 v11
        -> coe
             seq (coe v8)
             (coe
                du_resolveExprWF_6668 (coe v0) (coe v1) (coe v6)
                (coe d_removePoly_324 (coe v5) (coe v2)) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1094 (coe v1)
                   (coe v6) (coe v9)))
      C_failure_278 v8
        -> coe MAlonzo.Code.Once.Surface.Syntax.C_poly_504 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.resolveExpr
d_resolveExpr_7076 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
d_resolveExpr_7076 v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_resolveExpr_7076 v0 v1 v3 v4 v5 v6 v7
du_resolveExpr_7076 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174
du_resolveExpr_7076 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_resolveExprWF_6668 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6)
-- Once.TypeCheck.Elaborate.resolveExpr-var
d_resolveExpr'45'var_7098 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'var_7098 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-lam
d_resolveExpr'45'lam_7124 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'lam_7124 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-app
d_resolveExpr'45'app_7150 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'app_7150 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-pair
d_resolveExpr'45'pair_7174 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'pair_7174 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-effApp
d_resolveExpr'45'effApp_7198 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'effApp_7198 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-fst'
d_resolveExpr'45'fst''_7218 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'fst''_7218 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-snd'
d_resolveExpr'45'snd''_7238 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'snd''_7238 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-inl'
d_resolveExpr'45'inl''_7258 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inl''_7258 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-inr'
d_resolveExpr'45'inr''_7278 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'inr''_7278 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-case'
d_resolveExpr'45'case''_7312 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'case''_7312 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-unit
d_resolveExpr'45'unit_7324 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'unit_7324 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-absurd
d_resolveExpr'45'absurd_7342 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'absurd_7342 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-let'
d_resolveExpr'45'let''_7368 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'let''_7368 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-int
d_resolveExpr'45'int_7382 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'int_7382 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-str
d_resolveExpr'45'str_7396 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'str_7396 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-add
d_resolveExpr'45'add_7416 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'add_7416 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-sub
d_resolveExpr'45'sub_7436 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'sub_7436 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-mul
d_resolveExpr'45'mul_7456 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'mul_7456 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-div
d_resolveExpr'45'div_7476 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'div_7476 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-mod'
d_resolveExpr'45'mod''_7496 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'mod''_7496 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-neg
d_resolveExpr'45'neg_7512 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'neg_7512 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-lt
d_resolveExpr'45'lt_7532 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'lt_7532 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-le
d_resolveExpr'45'le_7552 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'le_7552 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-gt
d_resolveExpr'45'gt_7572 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'gt_7572 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-ge
d_resolveExpr'45'ge_7592 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'ge_7592 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-eq
d_resolveExpr'45'eq_7612 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'eq_7612 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-ne
d_resolveExpr'45'ne_7632 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'ne_7632 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-arr'
d_resolveExpr'45'arr''_7652 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'arr''_7652 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-sigOp
d_resolveExpr'45'sigOp_7668 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'sigOp_7668 = erased
-- Once.TypeCheck.Elaborate.acc-step-at-poly
d_acc'45'step'45'at'45'poly_7676 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_acc'45'step'45'at'45'poly_7676 = erased
-- Once.TypeCheck.Elaborate.applySplice-eq-irrel
d_applySplice'45'eq'45'irrel_7712 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_238 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_CheckElabResult_262 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_applySplice'45'eq'45'irrel_7712 = erased
-- Once.TypeCheck.Elaborate.resolveExpr-poly-match
d_resolveExpr'45'poly'45'match_7774 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_238 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveExpr'45'poly'45'match_7774 = erased
-- Once.TypeCheck.Elaborate.checkElab-fallback-RVar-poly
d_checkElab'45'fallback'45'RVar'45'poly_7818 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_238 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar'45'poly_7818 v0 v1 ~v2 ~v3 ~v4 ~v5
                                             ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
  = du_checkElab'45'fallback'45'RVar'45'poly_7818 v0 v1
du_checkElab'45'fallback'45'RVar'45'poly_7818 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar'45'poly_7818 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v1))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                 (coe ("unit" :: Data.Text.Text))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_504 v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe d_freshCounter_430 (coe v0)) erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-id
d_checkElab'45'fallback'45'RApp'45'id_7910 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'id_7910 ~v0 ~v1 v2 ~v3 v4 v5 v6
                                           ~v7
  = du_checkElab'45'fallback'45'RApp'45'id_7910 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'id_7910 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'id_7910 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-fst
d_checkElab'45'fallback'45'RApp'45'fst_7960 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'fst_7960 ~v0 ~v1 v2 ~v3 v4 v5 v6
                                            ~v7
  = du_checkElab'45'fallback'45'RApp'45'fst_7960 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'fst_7960 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'fst_7960 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-snd
d_checkElab'45'fallback'45'RApp'45'snd_8010 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'snd_8010 ~v0 ~v1 v2 ~v3 v4 v5 v6
                                            ~v7
  = du_checkElab'45'fallback'45'RApp'45'snd_8010 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'snd_8010 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'snd_8010 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-generic
d_checkElab'45'fallback'45'RApp'45'generic_8062 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'generic_8062 ~v0 ~v1 ~v2 v3 ~v4
                                                v5 v6 v7 ~v8 ~v9
  = du_checkElab'45'fallback'45'RApp'45'generic_8062 v3 v5 v6 v7
du_checkElab'45'fallback'45'RApp'45'generic_8062 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'generic_8062 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RApp-terminal
d_checkElab'45'fallback'45'RApp'45'terminal_8132 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RApp'45'terminal_8132 ~v0 ~v1 v2 ~v3 v4
                                                 v5 v6 ~v7
  = du_checkElab'45'fallback'45'RApp'45'terminal_8132 v2 v4 v5 v6
du_checkElab'45'fallback'45'RApp'45'terminal_8132 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RApp'45'terminal_8132 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElab-fallback-RBinOp
d_checkElab'45'fallback'45'RBinOp_8186 ::
  T_NamedCtx_410 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RBinOp_8186 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7
                                       v8 ~v9
  = du_checkElab'45'fallback'45'RBinOp_8186 v4 v6 v7 v8
du_checkElab'45'fallback'45'RBinOp_8186 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RBinOp_8186 v0 v1 v2 v3
  = let v4 = d__'8799'T__176 (coe v0) (coe v0) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased)))
                else coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExprTyped
d_compileExprTyped_8230 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.CCC.IR.T_IR_264
d_compileExprTyped_8230 v0 v1
  = let v2
          = d_checkElab_1846 (coe d_emptyCtx_438) (coe v0) (coe v1) in
    coe
      (case coe v2 of
         C_success_276 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_114
                   (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v1)
                   (coe v4))
         C_failure_278 v3
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.compileExpr
d_compileExpr_8254 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compileExpr_8254 v0
  = let v1 = d_inferElab_1840 (coe d_emptyCtx_438) (coe v0) in
    coe
      (case coe v1 of
         C_success_252 v2 v3 v4 v5 v6
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Surface.Elaborate.du_elaborate_114
                      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8) (coe v2)
                      (coe v4)))
         C_failure_254 v2
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> MAlonzo.RTE.mazUnreachableError)
