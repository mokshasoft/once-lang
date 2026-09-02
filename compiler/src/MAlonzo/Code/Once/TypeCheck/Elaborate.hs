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
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.SigEffect
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Surface.Thinning
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Error
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
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
  = let v3
          = let v3
                  = case coe v2 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
                        -> coe
                             seq (coe v3)
                             (coe
                                seq (coe v4)
                                (coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                   (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                      _ -> MAlonzo.RTE.mazUnreachableError in
            coe
              (case coe v0 of
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                   -> case coe v4 of
                        MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                          -> case coe v5 of
                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                 -> coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                      (coe v4)
                                      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                               _ -> coe v3
                        _ -> coe v3
                 _ -> MAlonzo.RTE.mazUnreachableError) in
    coe
      (case coe v1 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> let v6
                    = let v6
                            = case coe v2 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                                  -> case coe v6 of
                                       MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                         -> case coe v7 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                -> coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v6)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                              _ -> coe v3
                                       _ -> coe v3
                                _ -> MAlonzo.RTE.mazUnreachableError in
                      coe
                        (case coe v0 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                             -> case coe v7 of
                                  MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                    -> case coe v8 of
                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                           -> coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v7)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                         _ -> coe v6
                                  _ -> coe v6
                           _ -> MAlonzo.RTE.mazUnreachableError) in
              coe
                (if coe v4
                   then let v7
                              = case coe v2 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                    -> case coe v7 of
                                         MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                           -> case coe v8 of
                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                  -> coe
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                       (coe v7)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                _ -> coe v6
                                         _ -> coe v6
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v0 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                               -> let v10
                                        = case coe v2 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                              -> case coe v10 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v11 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v10)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v7
                                                   _ -> coe v7
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v8
                                       then case coe v2 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                -> if coe v11
                                                     then case coe v9 of
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                              -> case coe v5 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v14
                                                                     -> case coe v12 of
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                            -> coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                 (coe v11)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                    erased)
                                                                          _ -> coe v10
                                                                   _ -> coe v10
                                                            _ -> coe v10
                                                     else (case coe v12 of
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                               -> coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                    (coe v11)
                                                                    (coe
                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                             _ -> coe v10)
                                              _ -> MAlonzo.RTE.mazUnreachableError
                                       else (case coe v9 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v8)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v10))
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   else (case coe v5 of
                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                             -> coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe v4)
                                  (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                           _ -> coe v6))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.≟T-μ-aux
d_'8799'T'45'μ'45'aux_134 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'T'45'μ'45'aux_134 ~v0 ~v1 v2
  = du_'8799'T'45'μ'45'aux_134 v2
du_'8799'T'45'μ'45'aux_134 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'T'45'μ'45'aux_134 v0
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
d_'8799'T'45'ν'45'aux_144 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'T'45'ν'45'aux_144 ~v0 ~v1 v2
  = du_'8799'T'45'ν'45'aux_144 v2
du_'8799'T'45'ν'45'aux_144 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'T'45'ν'45'aux_144 v0
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
-- Once.TypeCheck.Elaborate.isRIntVliftTarget?
d_isRIntVliftTarget'63'_156 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isRIntVliftTarget'63'_156 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                           erased))
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.isRFloatVliftTarget?
d_isRFloatVliftTarget'63'_168 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_isRFloatVliftTarget'63'_168 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                           erased))
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.RPairTarget
d_RPairTarget_174 a0 = ()
data T_RPairTarget_174
  = C_rpt'45'prod_180 | C_rpt'45'vlift_190 | C_rpt'45'other_194
-- Once.TypeCheck.Elaborate.classifyRPairTarget
d_classifyRPairTarget_198 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_RPairTarget_174
d_classifyRPairTarget_198 v0
  = let v1 = coe C_rpt'45'other_194 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'42'__122 v2 v3 -> coe C_rpt'45'prod_180
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v4 of
                              MAlonzo.Code.Once.Type.C__'42'__122 v7 v8 -> coe C_rpt'45'vlift_190
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.Elaborate._≟F_
d__'8799'F__218 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'F__218 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_K_110 v3
               -> coe
                    du_'8799'F'45'K'45'aux_10 (coe d__'8799'T__224 (coe v2) (coe v3))
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
                    (coe d__'8799'F__218 (coe v2) (coe v4))
                    (coe d__'8799'F__218 (coe v3) (coe v5))
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
                    (coe d__'8799'F__218 (coe v2) (coe v4))
                    (coe d__'8799'F__218 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate._≟T_
d__'8799'T__224 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'T__224 v0 v1
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
                    (coe d__'8799'T__224 (coe v2) (coe v4))
                    (coe d__'8799'T__224 (coe v3) (coe v5))
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
                    (coe d__'8799'T__224 (coe v2) (coe v4))
                    (coe d__'8799'T__224 (coe v3) (coe v5))
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
                    (coe d__'8799'T__224 (coe v2) (coe v5))
                    (coe MAlonzo.Code.Once.Type.d__'8799'k__96 (coe v3) (coe v6))
                    (coe d__'8799'T__224 (coe v4) (coe v7))
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
                    du_'8799'T'45'μ'45'aux_134 (coe d__'8799'F__218 (coe v2) (coe v3))
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
                    du_'8799'T'45'ν'45'aux_144 (coe d__'8799'F__218 (coe v2) (coe v3))
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
d_InferElabResult_286 a0 a1 = ()
data T_InferElabResult_286
  = C_success_300 MAlonzo.Code.Once.Type.T_Type_108
                  MAlonzo.Code.Once.Surface.Context.T_Usage_60
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_failure_302 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.CheckElabResult
d_CheckElabResult_310 a0 a1 a2 = ()
data T_CheckElabResult_310
  = C_success_324 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_failure_326 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.NegOperandView
d_NegOperandView_328 a0 = ()
data T_NegOperandView_328
  = C_nov'45'int_332 | C_nov'45'float_342 | C_nov'45'other_346
-- Once.TypeCheck.Elaborate.negOperandView
d_negOperandView_350 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NegOperandView_328
d_negOperandView_350 v0
  = let v1 = coe C_nov'45'other_346 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v2
           -> coe C_nov'45'int_332
         MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v2 v3 v4 v5
           -> coe C_nov'45'float_342
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.soundOf
d_soundOf_368 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_286 -> ()
d_soundOf_368 = erased
-- Once.TypeCheck.Elaborate.VerifiedInferResult
d_VerifiedInferResult_392 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_VerifiedInferResult_392 = erased
-- Once.TypeCheck.Elaborate.checkSoundOf
d_checkSoundOf_406 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_310 -> ()
d_checkSoundOf_406 = erased
-- Once.TypeCheck.Elaborate.VerifiedCheckResult
d_VerifiedCheckResult_434 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_VerifiedCheckResult_434 = erased
-- Once.TypeCheck.Elaborate.EffArrowView
d_EffArrowView_444 a0 = ()
data T_EffArrowView_444 = C_eav'45'eff_450 | C_eav'45'other_454
-- Once.TypeCheck.Elaborate.classifyEffArrow
d_classifyEffArrow_458 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> T_EffArrowView_444
d_classifyEffArrow_458 v0
  = let v1 = coe C_eav'45'other_454 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v6 of
                              MAlonzo.Code.Once.Type.C_eff_36 -> coe C_eav'45'eff_450
                              _ -> coe v1
                       _ -> coe v1
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Once.TypeCheck.Elaborate.embedOrSubsume-no
d_embedOrSubsume'45'no_480 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume'45'no_480 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_embedOrSubsume'45'no_480 v2 v3 v4 v5 v6 v7 v8
du_embedOrSubsume'45'no_480 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume'45'no_480 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_326
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60 (coe v1)
                    (coe v2)))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v8 v9 v10
           -> case coe v9 of
                MAlonzo.Code.Once.Type.C_mk'45'kind_50 v11 v12
                  -> case coe v11 of
                       MAlonzo.Code.Once.Type.C_Many_10
                         -> case coe v12 of
                              MAlonzo.Code.Once.Type.C_eff_36
                                -> case coe v2 of
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                       -> case coe v14 of
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                                              -> case coe v16 of
                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                     -> case coe v17 of
                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                            -> let v18
                                                                     = d__'8799'T__224
                                                                         (coe v8) (coe v13) in
                                                               coe
                                                                 (let v19
                                                                        = d__'8799'T__224
                                                                            (coe v10) (coe v15) in
                                                                  coe
                                                                    (case coe v18 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                         -> let v22
                                                                                  = coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                      (coe
                                                                                         C_failure_326
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                               (coe
                                                                                                  v8)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                  (coe
                                                                                                     v16)
                                                                                                  (coe
                                                                                                     v12))
                                                                                               (coe
                                                                                                  v10))
                                                                                            (coe
                                                                                               v2)))
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
                                                                            coe
                                                                              (case coe v20 of
                                                                                 MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                   -> case coe
                                                                                             v21 of
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v23
                                                                                          -> case coe
                                                                                                    v19 of
                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                                 -> case coe
                                                                                                           v24 of
                                                                                                      MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                        -> case coe
                                                                                                                  v25 of
                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v26
                                                                                                               -> coe
                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                    (coe
                                                                                                                       C_success_324
                                                                                                                       (coe
                                                                                                                          v0)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                                                          v3)
                                                                                                                       (coe
                                                                                                                          v4)
                                                                                                                       (coe
                                                                                                                          v5))
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516
                                                                                                                          v6))
                                                                                                             _ -> coe
                                                                                                                    v22
                                                                                                      _ -> coe
                                                                                                             v22
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> coe v22
                                                                                 _ -> coe v22)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                          _ -> coe v7
                                                   _ -> coe v7
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v7
                              _ -> coe v7
                       _ -> coe v7
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v7)
-- Once.TypeCheck.Elaborate.embedOrSubsume
d_embedOrSubsume_568 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume_568 ~v0 ~v1 v2 v3 = du_embedOrSubsume_568 v2 v3
du_embedOrSubsume_568 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume_568 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_300 v4 v5 v6 v7 v8
               -> let v9 = d__'8799'T__224 (coe v0) (coe v4) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                         -> if coe v10
                              then coe
                                     seq (coe v11)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_success_324 (coe v5) (coe v6) (coe v7) (coe v8))
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516
                                           v3))
                              else coe
                                     seq (coe v11)
                                     (coe
                                        du_embedOrSubsume'45'no_480 (coe v5) (coe v0) (coe v4)
                                        (coe v6) (coe v7) (coe v8) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             C_failure_302 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v4))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.specId
d_specId_638 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specId_638 ~v0 = du_specId_638
du_specId_638 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specId_638
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
      (coe MAlonzo.Code.Once.IR.C_id_22)
-- Once.TypeCheck.Elaborate.specFst
d_specFst_646 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specFst_646 ~v0 ~v1 = du_specFst_646
du_specFst_646 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specFst_646
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
      (coe MAlonzo.Code.Once.IR.C_fst_44)
-- Once.TypeCheck.Elaborate.specSnd
d_specSnd_656 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specSnd_656 ~v0 ~v1 = du_specSnd_656
du_specSnd_656 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specSnd_656
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
      (coe MAlonzo.Code.Once.IR.C_snd_50)
-- Once.TypeCheck.Elaborate.specInl
d_specInl_666 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInl_666 ~v0 ~v1 = du_specInl_666
du_specInl_666 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInl_666
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
      (coe
         MAlonzo.Code.Once.IR.C_inl_56 (coe MAlonzo.Code.Once.IR.C_Heap_8))
-- Once.TypeCheck.Elaborate.specInr
d_specInr_676 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInr_676 ~v0 ~v1 = du_specInr_676
du_specInr_676 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInr_676
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
      (coe
         MAlonzo.Code.Once.IR.C_inr_62 (coe MAlonzo.Code.Once.IR.C_Heap_8))
-- Once.TypeCheck.Elaborate.specUnitGen
d_specUnitGen_682 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specUnitGen_682 = coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152
-- Once.TypeCheck.Elaborate.specPair
d_specPair_690 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specPair_690 v0 ~v1 ~v2 = du_specPair_690 v0
du_specPair_690 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specPair_690 v0
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32
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
         MAlonzo.Code.Once.Surface.Syntax.C_lam_32
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
            MAlonzo.Code.Once.Surface.Syntax.C_lam_32
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
               MAlonzo.Code.Once.Surface.Syntax.C_pair_76
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_48
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_48
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specTerminal
d_specTerminal_700 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specTerminal_700 ~v0 = du_specTerminal_700
du_specTerminal_700 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specTerminal_700
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
      (coe MAlonzo.Code.Once.IR.C_terminal_74)
-- Once.TypeCheck.Elaborate.specInitial
d_specInitial_706 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specInitial_706 ~v0 = du_specInitial_706
du_specInitial_706 :: MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specInitial_706
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
      (coe MAlonzo.Code.Once.IR.C_initial_78)
-- Once.TypeCheck.Elaborate.specCurry
d_specCurry_716 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCurry_716 v0 v1 ~v2 = du_specCurry_716 v0 v1
du_specCurry_716 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCurry_716 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32
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
         MAlonzo.Code.Once.Surface.Syntax.C_lam_32
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
            MAlonzo.Code.Once.Surface.Syntax.C_lam_32
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
               MAlonzo.Code.Once.Surface.Syntax.C_app_48
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe MAlonzo.Code.Once.Type.C_One_8))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v0) (coe v1))
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_16
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_pair_76
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specApply
d_specApply_728 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specApply_728 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Type.C_One_8)))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_app_48
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))
         v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_fst''_88 v0
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_16
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_snd''_100
            (MAlonzo.Code.Once.Type.d__'8658'__146 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_var_16
               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
-- Once.TypeCheck.Elaborate.specCompose
d_specCompose_740 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCompose_740 v0 v1 ~v2 = du_specCompose_740 v0 v1
du_specCompose_740 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCompose_740 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32
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
         MAlonzo.Code.Once.Surface.Syntax.C_lam_32
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
            MAlonzo.Code.Once.Surface.Syntax.C_lam_32
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
               MAlonzo.Code.Once.Surface.Syntax.C_app_48
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_16
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_48
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.specCase
d_specCase_754 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
d_specCase_754 v0 v1 ~v2 = du_specCase_754 v0 v1
du_specCase_754 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8
du_specCase_754 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_Zero_6)
         (coe
            MAlonzo.Code.Once.Type.d__'8852'q__24
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
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
      (coe
         MAlonzo.Code.Once.Surface.Syntax.C_lam_32
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'8852'q__24
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
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_lam_32
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_One_8)
               (coe
                  MAlonzo.Code.Once.Type.d__'8852'q__24
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
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
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
            (coe
               MAlonzo.Code.Once.Surface.Syntax.C_case''_146
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62))))
               (MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8)))
               (MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8)))
               v0 v1
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_var_16
                  (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_48
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_One_8)
                              (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)))))
                  v0 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
               (coe
                  MAlonzo.Code.Once.Surface.Syntax.C_app_48
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)))))
                  v1 (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe
                        MAlonzo.Code.Data.Fin.Base.C_suc_16
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Once.Surface.Syntax.C_var_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))))
-- Once.TypeCheck.Elaborate.extract-morph-aux
d_extract'45'morph'45'aux_778 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extract'45'morph'45'aux_778 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_extract'45'morph'45'aux_778 v3 v7
du_extract'45'morph'45'aux_778 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph'45'aux_778 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased)
                _ -> coe v2
         _ -> coe v2)
-- Once.TypeCheck.Elaborate.extract-morph
d_extract'45'morph_796 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extract'45'morph_796 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_extract'45'morph_796 v3 v4 v5 v6
du_extract'45'morph_796 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extract'45'morph_796 v0 v1 v2 v3
  = coe
      du_extract'45'morph'45'aux_778
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v0)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v2))
         (coe v1))
      (coe v3)
-- Once.TypeCheck.Elaborate.WellFormedFView
d_WellFormedFView_802 a0 = ()
data T_WellFormedFView_802
  = C_wfv'45'yes_808 MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 |
    C_wfv'45'no_810
-- Once.TypeCheck.Elaborate.inspectWellFormedF
d_inspectWellFormedF_814 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> T_WellFormedFView_802
d_inspectWellFormedF_814 v0
  = let v1
          = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
              (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> coe C_wfv'45'yes_808 v2
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_wfv'45'no_810
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.AppSpine
d_AppSpine_830 = ()
data T_AppSpine_830
  = C_mkSpine_840 MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
                  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
-- Once.TypeCheck.Elaborate.AppSpine.head
d_head_836 ::
  T_AppSpine_830 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_head_836 v0
  = case coe v0 of
      C_mkSpine_840 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.AppSpine.args
d_args_838 ::
  T_AppSpine_830 -> [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34]
d_args_838 v0
  = case coe v0 of
      C_mkSpine_840 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.spineOf
d_spineOf_842 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppSpine_830
d_spineOf_842 v0
  = coe
      du_go_850 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.TypeCheck.Elaborate._.go
d_go_850 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_830
d_go_850 ~v0 v1 v2 = du_go_850 v1 v2
du_go_850 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34] -> T_AppSpine_830
du_go_850 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v2
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v2 v3
        -> coe
             du_go_850 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v2 v3
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v2 v3 v4
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v2 v3
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v2 v3 v4 v5 v6
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v2
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v2 v3 v4 v5
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v2
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v2 v3
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v2 v3 v4
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v3
        -> coe
             C_mkSpine_840
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v3) (coe v1)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v2 v3
        -> coe C_mkSpine_840 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.isPolyBuiltin
d_isPolyBuiltin_950 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d_isPolyBuiltin_950 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         l | (==) l ("apply" :: Data.Text.Text) ->
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
-- Once.TypeCheck.Elaborate.matchInferResult
d_matchInferResult_958 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_286 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_310
d_matchInferResult_958 ~v0 ~v1 v2 v3
  = du_matchInferResult_958 v2 v3
du_matchInferResult_958 ::
  T_InferElabResult_286 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_310
du_matchInferResult_958 v0 v1
  = case coe v0 of
      C_success_300 v2 v3 v4 v5 v6
        -> let v7 = d__'8799'T__224 (coe v1) (coe v2) in
           coe
             (case coe v7 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                  -> if coe v8
                       then coe
                              seq (coe v9)
                              (coe C_success_324 (coe v3) (coe v4) (coe v5) (coe v6))
                       else coe
                              seq (coe v9)
                              (coe
                                 C_failure_326
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60 (coe v1)
                                    (coe v2)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_failure_302 v2 -> coe C_failure_326 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.FunProjection
d_FunProjection_1006 a0 a1 = ()
data T_FunProjection_1006
  = C_isFun_1020 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Type.T_Quantity_4
                 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_isEff_1028 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Type.T_Type_108
                 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_notFun_1030 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asFun
d_asFun_1036 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_286 -> T_FunProjection_1006
d_asFun_1036 ~v0 ~v1 v2 = du_asFun_1036 v2
du_asFun_1036 :: T_InferElabResult_286 -> T_FunProjection_1006
du_asFun_1036 v0
  = case coe v0 of
      C_success_300 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    C_notFun_1030
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    C_notFun_1030
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> coe
                    C_notFun_1030
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    C_notFun_1030
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Once.Type.C_pure_34
                             -> coe
                                  C_isFun_1020 (coe v6) (coe v9) (coe v8) (coe v2) (coe v3) (coe v4)
                                  (coe v5)
                           MAlonzo.Code.Once.Type.C_eff_36
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         C_notFun_1030
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                            (coe v1))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         C_notFun_1030
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                            (coe v1))
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe
                                         C_isEff_1028 (coe v6) (coe v8) (coe v2) (coe v3) (coe v4)
                                         (coe v5)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    C_notFun_1030
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6
               -> coe
                    C_notFun_1030
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    C_notFun_1030
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    C_notFun_1030
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    C_notFun_1030
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    C_notFun_1030
                    (coe MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_302 v1 -> coe C_notFun_1030 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.IntProjection
d_IntProjection_1102 a0 a1 = ()
data T_IntProjection_1102
  = C_isInt_1110 MAlonzo.Code.Once.Surface.Context.T_Usage_60
                 MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 Integer Integer |
    C_notInt_1112 MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
-- Once.TypeCheck.Elaborate.asInt
d_asInt_1118 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_286 -> T_IntProjection_1102
d_asInt_1118 ~v0 ~v1 v2 = du_asInt_1118 v2
du_asInt_1118 :: T_InferElabResult_286 -> T_IntProjection_1102
du_asInt_1118 v0
  = case coe v0 of
      C_success_300 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    C_notInt_1112
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    C_notInt_1112
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> coe
                    C_notInt_1112
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    C_notInt_1112
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> coe
                    C_notInt_1112
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    C_notInt_1112
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6
               -> coe
                    C_notInt_1112
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe C_isInt_1110 (coe v2) (coe v3) (coe v4) (coe v5)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    C_notInt_1112
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    C_notInt_1112
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    C_notInt_1112
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_302 v1 -> coe C_notInt_1112 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.notNumeric
d_notNumeric_1152 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  T_InferElabResult_286 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
d_notNumeric_1152 ~v0 ~v1 v2 = du_notNumeric_1152 v2
du_notNumeric_1152 ::
  T_InferElabResult_286 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6
du_notNumeric_1152 v0
  = case coe v0 of
      C_success_300 v1 v2 v3 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_failure_302 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.decideLeq
d_decideLeq_1178 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decideLeq_1178 v0 v1
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
-- Once.TypeCheck.Elaborate.inferElab-RApp-id
d_inferElab'45'RApp'45'id_1182 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  T_InferElabResult_286 -> T_InferElabResult_286
d_inferElab'45'RApp'45'id_1182 v0 v1
  = case coe v1 of
      C_success_300 v2 v3 v4 v5 v6
        -> coe
             C_success_300 (coe v2)
             (coe
                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                (coe
                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3)))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v3 v2
                (coe MAlonzo.Code.Once.IR.C_id_22) v4)
             (coe addInt (coe (1 :: Integer)) (coe v5)) (coe v6)
      C_failure_302 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.bbc-other-poly-witness
d_bbc'45'other'45'poly'45'witness_1206
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Elaborate.bbc-other-poly-witness"
-- Once.TypeCheck.Elaborate.bbc-other-poly-infer-witness
d_bbc'45'other'45'poly'45'infer'45'witness_1214
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Elaborate.bbc-other-poly-infer-witness"
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-ground-aux
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_1224 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'ground'45'aux_1224 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1224 v0 v1 v2 v3
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1224 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1224 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_300
                (coe MAlonzo.Code.Once.Type.d_extractGround_316 (coe v2) (coe v4))
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v1)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
             (coe
                d_bbc'45'other'45'poly'45'infer'45'witness_1214 v0 v1
                (MAlonzo.Code.Once.Type.d_extractGround_316 (coe v2) (coe v4)))
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
        -> coe
             seq (coe v4)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   C_failure_302
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v1)))
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-lookup-aux
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1246 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1246 v0 v1 v2 ~v3
  = du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1246 v0 v1 v2
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1246 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1246 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du_inferElabV'45'RVar'45'poly'45'ground'45'aux_1224 (coe v0)
                    (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.Type.d_isGround_432 (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-poly-aux
d_inferElabV'45'RVar'45'poly'45'aux_1266 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_BareBuiltinClass_1770 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'poly'45'aux_1266 v0 v1 v2 ~v3
  = du_inferElabV'45'RVar'45'poly'45'aux_1266 v0 v1 v2
du_inferElabV'45'RVar'45'poly'45'aux_1266 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_BareBuiltinClass_1770 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'poly'45'aux_1266 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1772
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("id" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1774
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("fst" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1776
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("snd" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1778
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("terminal" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1780
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("initial" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1782
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inl" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1784
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inr" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1788
        -> coe
             du_inferElabV'45'RVar'45'poly'45'lookup'45'aux_1246 (coe v0)
             (coe v1)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_48
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364 (coe v0))
                (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab
d_inferElab_1302 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_286
d_inferElab_1302 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_inferElabV_1460 (coe v0) (coe v1))
-- Once.TypeCheck.Elaborate.checkElab
d_checkElab_1308 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_310
d_checkElab_1308 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_checkElabV_1468 (coe v0) (coe v1) (coe v2))
-- Once.TypeCheck.Elaborate.checkElab-RVar
d_checkElab'45'RVar_1316 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_CheckElabResult_310
d_checkElab'45'RVar_1316 v0 v1 v2
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
                then let v6
                           = seq
                               (coe v5)
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1772) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1772
                            -> let v7
                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_inferElabV_1460 (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                               (coe
                                                  MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe ("Generators" :: Data.Text.Text))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe ("id" :: Data.Text.Text))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                               coe
                                 (case coe v7 of
                                    C_success_300 v8 v9 v10 v11 v12
                                      -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                -> if coe v14
                                                     then coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_success_324 (coe v9) (coe v10)
                                                               (coe v11) (coe v12))
                                                     else coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_failure_326
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                  (coe v2) (coe v8)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_302 v8
                                      -> let v9 = coe C_failure_326 (coe v8) in
                                         coe
                                           (case coe v2 of
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                -> case coe v11 of
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                                     -> let v15
                                                                              = d__'8799'T__224
                                                                                  (coe v10)
                                                                                  (coe v12) in
                                                                        coe
                                                                          (case coe v15 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                               -> if coe v16
                                                                                    then coe
                                                                                           seq
                                                                                           (coe v17)
                                                                                           (coe
                                                                                              C_success_324
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                    (coe
                                                                                                       v0)))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                                    (coe
                                                                                                       v0))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                    (coe
                                                                                                       v10)
                                                                                                    (coe
                                                                                                       v11)
                                                                                                    (coe
                                                                                                       v10))
                                                                                                 (coe
                                                                                                    du_specId_638))
                                                                                              (coe
                                                                                                 (0 ::
                                                                                                    Integer))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                                 (coe
                                                                                                    v0)))
                                                                                    else coe
                                                                                           seq
                                                                                           (coe v17)
                                                                                           (coe
                                                                                              C_failure_326
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                                 (coe
                                                                                                    ("id"
                                                                                                     ::
                                                                                                     Data.Text.Text))))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                   _ -> coe v9
                                                            _ -> coe v9
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1774
                            -> let v7
                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_inferElabV_1460 (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                               (coe
                                                  MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe ("Generators" :: Data.Text.Text))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe ("fst" :: Data.Text.Text))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                               coe
                                 (case coe v7 of
                                    C_success_300 v8 v9 v10 v11 v12
                                      -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                -> if coe v14
                                                     then coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_success_324 (coe v9) (coe v10)
                                                               (coe v11) (coe v12))
                                                     else coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_failure_326
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                  (coe v2) (coe v8)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_302 v8
                                      -> let v9 = coe C_failure_326 (coe v8) in
                                         coe
                                           (case coe v2 of
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                -> case coe v10 of
                                                     MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                                       -> case coe v11 of
                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                              -> case coe v15 of
                                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                                     -> case coe v16 of
                                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                                            -> let v17
                                                                                     = d__'8799'T__224
                                                                                         (coe v13)
                                                                                         (coe
                                                                                            v12) in
                                                                               coe
                                                                                 (case coe v17 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                      -> if coe v18
                                                                                           then coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     C_success_324
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                           (coe
                                                                                                              v0)))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                                           (coe
                                                                                                              v0))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                           (coe
                                                                                                              v10)
                                                                                                           (coe
                                                                                                              v11)
                                                                                                           (coe
                                                                                                              v13))
                                                                                                        (coe
                                                                                                           du_specFst_646))
                                                                                                     (coe
                                                                                                        (0 ::
                                                                                                           Integer))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                                        (coe
                                                                                                           v0)))
                                                                                           else coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     C_failure_326
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                                        (coe
                                                                                                           ("fst"
                                                                                                            ::
                                                                                                            Data.Text.Text))))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> coe v9
                                                                   _ -> coe v9
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> coe v9
                                              _ -> coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1776
                            -> let v7
                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_inferElabV_1460 (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                               (coe
                                                  MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe ("Generators" :: Data.Text.Text))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe ("snd" :: Data.Text.Text))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                               coe
                                 (case coe v7 of
                                    C_success_300 v8 v9 v10 v11 v12
                                      -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                -> if coe v14
                                                     then coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_success_324 (coe v9) (coe v10)
                                                               (coe v11) (coe v12))
                                                     else coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_failure_326
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                  (coe v2) (coe v8)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_302 v8
                                      -> let v9 = coe C_failure_326 (coe v8) in
                                         coe
                                           (case coe v2 of
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                -> case coe v10 of
                                                     MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                                       -> case coe v11 of
                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                              -> case coe v15 of
                                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                                     -> case coe v16 of
                                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                                            -> let v17
                                                                                     = d__'8799'T__224
                                                                                         (coe v14)
                                                                                         (coe
                                                                                            v12) in
                                                                               coe
                                                                                 (case coe v17 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                      -> if coe v18
                                                                                           then coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     C_success_324
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                           (coe
                                                                                                              v0)))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                                           (coe
                                                                                                              v0))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                           (coe
                                                                                                              v10)
                                                                                                           (coe
                                                                                                              v11)
                                                                                                           (coe
                                                                                                              v14))
                                                                                                        (coe
                                                                                                           du_specSnd_656))
                                                                                                     (coe
                                                                                                        (0 ::
                                                                                                           Integer))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                                        (coe
                                                                                                           v0)))
                                                                                           else coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     C_failure_326
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                                        (coe
                                                                                                           ("snd"
                                                                                                            ::
                                                                                                            Data.Text.Text))))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> coe v9
                                                                   _ -> coe v9
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> coe v9
                                              _ -> coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1778
                            -> let v7
                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_inferElabV_1460 (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                               (coe
                                                  MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe ("Generators" :: Data.Text.Text))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe ("terminal" :: Data.Text.Text))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                               coe
                                 (case coe v7 of
                                    C_success_300 v8 v9 v10 v11 v12
                                      -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                -> if coe v14
                                                     then coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_success_324 (coe v9) (coe v10)
                                                               (coe v11) (coe v12))
                                                     else coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_failure_326
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                  (coe v2) (coe v8)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_302 v8
                                      -> let v9 = coe C_failure_326 (coe v8) in
                                         coe
                                           (case coe v2 of
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                -> case coe v11 of
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                                     -> case coe v12 of
                                                                          MAlonzo.Code.Once.Type.C_Unit_118
                                                                            -> coe
                                                                                 C_success_324
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                       (coe v0)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                       (coe v0))
                                                                                    (coe v2)
                                                                                    (coe
                                                                                       du_specTerminal_700))
                                                                                 (coe
                                                                                    (0 :: Integer))
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                    (coe v0))
                                                                          _ -> coe v9
                                                                   _ -> coe v9
                                                            _ -> coe v9
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1780
                            -> let v7
                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_inferElabV_1460 (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                               (coe
                                                  MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe ("Generators" :: Data.Text.Text))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe ("initial" :: Data.Text.Text))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                               coe
                                 (case coe v7 of
                                    C_success_300 v8 v9 v10 v11 v12
                                      -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                -> if coe v14
                                                     then coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_success_324 (coe v9) (coe v10)
                                                               (coe v11) (coe v12))
                                                     else coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_failure_326
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                  (coe v2) (coe v8)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_302 v8
                                      -> let v9 = coe C_failure_326 (coe v8) in
                                         coe
                                           (case coe v2 of
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                -> case coe v10 of
                                                     MAlonzo.Code.Once.Type.C_Void_120
                                                       -> case coe v11 of
                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                                              -> case coe v13 of
                                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                                     -> case coe v14 of
                                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                                            -> coe
                                                                                 C_success_324
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                       (coe v0)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                       (coe v0))
                                                                                    (coe v2)
                                                                                    (coe
                                                                                       du_specInitial_706))
                                                                                 (coe
                                                                                    (0 :: Integer))
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                    (coe v0))
                                                                          _ -> coe v9
                                                                   _ -> coe v9
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> coe v9
                                              _ -> coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1782
                            -> let v7
                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_inferElabV_1460 (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                               (coe
                                                  MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe ("Generators" :: Data.Text.Text))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe ("inl" :: Data.Text.Text))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                               coe
                                 (case coe v7 of
                                    C_success_300 v8 v9 v10 v11 v12
                                      -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                -> if coe v14
                                                     then coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_success_324 (coe v9) (coe v10)
                                                               (coe v11) (coe v12))
                                                     else coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_failure_326
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                  (coe v2) (coe v8)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_302 v8
                                      -> let v9 = coe C_failure_326 (coe v8) in
                                         coe
                                           (case coe v2 of
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                -> case coe v11 of
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                                     -> case coe v12 of
                                                                          MAlonzo.Code.Once.Type.C__'43'__124 v15 v16
                                                                            -> let v17
                                                                                     = d__'8799'T__224
                                                                                         (coe v10)
                                                                                         (coe
                                                                                            v15) in
                                                                               coe
                                                                                 (case coe v17 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                      -> if coe v18
                                                                                           then coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     C_success_324
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                           (coe
                                                                                                              v0)))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                                           (coe
                                                                                                              v0))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                           (coe
                                                                                                              v10)
                                                                                                           (coe
                                                                                                              v11)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.Type.C__'43'__124
                                                                                                              (coe
                                                                                                                 v10)
                                                                                                              (coe
                                                                                                                 v16)))
                                                                                                        (coe
                                                                                                           du_specInl_666))
                                                                                                     (coe
                                                                                                        (0 ::
                                                                                                           Integer))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                                        (coe
                                                                                                           v0)))
                                                                                           else coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     C_failure_326
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                                        (coe
                                                                                                           ("inl"
                                                                                                            ::
                                                                                                            Data.Text.Text))))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> coe v9
                                                                   _ -> coe v9
                                                            _ -> coe v9
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1784
                            -> let v7
                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_inferElabV_1460 (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                               (coe
                                                  MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe ("Generators" :: Data.Text.Text))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe ("inr" :: Data.Text.Text))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                               coe
                                 (case coe v7 of
                                    C_success_300 v8 v9 v10 v11 v12
                                      -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                         coe
                                           (case coe v13 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                -> if coe v14
                                                     then coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_success_324 (coe v9) (coe v10)
                                                               (coe v11) (coe v12))
                                                     else coe
                                                            seq (coe v15)
                                                            (coe
                                                               C_failure_326
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                  (coe v2) (coe v8)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_302 v8
                                      -> let v9 = coe C_failure_326 (coe v8) in
                                         coe
                                           (case coe v2 of
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                -> case coe v11 of
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Once.Type.C_Many_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                                     -> case coe v12 of
                                                                          MAlonzo.Code.Once.Type.C__'43'__124 v15 v16
                                                                            -> let v17
                                                                                     = d__'8799'T__224
                                                                                         (coe v10)
                                                                                         (coe
                                                                                            v16) in
                                                                               coe
                                                                                 (case coe v17 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                      -> if coe v18
                                                                                           then coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     C_success_324
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                           (coe
                                                                                                              v0)))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                                           (coe
                                                                                                              v0))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                           (coe
                                                                                                              v10)
                                                                                                           (coe
                                                                                                              v11)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.Type.C__'43'__124
                                                                                                              (coe
                                                                                                                 v15)
                                                                                                              (coe
                                                                                                                 v10)))
                                                                                                        (coe
                                                                                                           du_specInr_676))
                                                                                                     (coe
                                                                                                        (0 ::
                                                                                                           Integer))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                                        (coe
                                                                                                           v0)))
                                                                                           else coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     C_failure_326
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                                        (coe
                                                                                                           ("inr"
                                                                                                            ::
                                                                                                            Data.Text.Text))))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> coe v9
                                                                   _ -> coe v9
                                                            _ -> coe v9
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v9)
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1788
                            -> let v8
                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            d_inferElabV_1460 (coe v0)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                               (coe v1))) in
                               coe
                                 (case coe v8 of
                                    C_success_300 v9 v10 v11 v12 v13
                                      -> let v14 = d__'8799'T__224 (coe v2) (coe v9) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                -> if coe v15
                                                     then coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_success_324 (coe v10) (coe v11)
                                                               (coe v12) (coe v13))
                                                     else coe
                                                            seq (coe v16)
                                                            (coe
                                                               C_failure_326
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                  (coe v2) (coe v9)))
                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                    C_failure_302 v9
                                      -> let v10
                                               = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_48
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                      (coe v0))
                                                   (coe v1) in
                                         coe
                                           (case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                -> coe
                                                     C_success_324
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                           (coe v0)))
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_poly_402
                                                        v1)
                                                     (coe (0 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                        (coe v0))
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe C_failure_326 (coe v9)
                                              _ -> MAlonzo.RTE.mazUnreachableError)
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
                                             then coe
                                                    seq (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1774)
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
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1776)
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
                                                                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1778)
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
                                                                                                                   MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1780)
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
                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1782)
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
                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1784)
                                                                                                                                                 else coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v23)
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1788)
                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                      _ -> MAlonzo.RTE.mazUnreachableError)) in
                      coe
                        (case coe v6 of
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1772
                             -> let v7
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_inferElabV_1460 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                                (coe
                                                   MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe ("Generators" :: Data.Text.Text))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe ("id" :: Data.Text.Text))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                                coe
                                  (case coe v7 of
                                     C_success_300 v8 v9 v10 v11 v12
                                       -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                          coe
                                            (case coe v13 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                 -> if coe v14
                                                      then coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_success_324 (coe v9) (coe v10)
                                                                (coe v11) (coe v12))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_failure_326
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                   (coe v2) (coe v8)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     C_failure_302 v8
                                       -> let v9 = coe C_failure_326 (coe v8) in
                                          coe
                                            (case coe v2 of
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                                        -> case coe v13 of
                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.Once.Type.C_pure_34
                                                                      -> let v15
                                                                               = d__'8799'T__224
                                                                                   (coe v10)
                                                                                   (coe v12) in
                                                                         coe
                                                                           (case coe v15 of
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                                -> if coe v16
                                                                                     then coe
                                                                                            seq
                                                                                            (coe
                                                                                               v17)
                                                                                            (coe
                                                                                               C_success_324
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                     (coe
                                                                                                        v0)))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                                     (coe
                                                                                                        v0))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                     (coe
                                                                                                        v10)
                                                                                                     (coe
                                                                                                        v11)
                                                                                                     (coe
                                                                                                        v10))
                                                                                                  (coe
                                                                                                     du_specId_638))
                                                                                               (coe
                                                                                                  (0 ::
                                                                                                     Integer))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                                  (coe
                                                                                                     v0)))
                                                                                     else coe
                                                                                            seq
                                                                                            (coe
                                                                                               v17)
                                                                                            (coe
                                                                                               C_failure_326
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                                  (coe
                                                                                                     ("id"
                                                                                                      ::
                                                                                                      Data.Text.Text))))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                    _ -> coe v9
                                                             _ -> coe v9
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> coe v9)
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1774
                             -> let v7
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_inferElabV_1460 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                                (coe
                                                   MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe ("Generators" :: Data.Text.Text))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe ("fst" :: Data.Text.Text))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                                coe
                                  (case coe v7 of
                                     C_success_300 v8 v9 v10 v11 v12
                                       -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                          coe
                                            (case coe v13 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                 -> if coe v14
                                                      then coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_success_324 (coe v9) (coe v10)
                                                                (coe v11) (coe v12))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_failure_326
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                   (coe v2) (coe v8)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     C_failure_302 v8
                                       -> let v9 = coe C_failure_326 (coe v8) in
                                          coe
                                            (case coe v2 of
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                                        -> case coe v11 of
                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                               -> case coe v15 of
                                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                                      -> case coe v16 of
                                                                           MAlonzo.Code.Once.Type.C_pure_34
                                                                             -> let v17
                                                                                      = d__'8799'T__224
                                                                                          (coe v13)
                                                                                          (coe
                                                                                             v12) in
                                                                                coe
                                                                                  (case coe v17 of
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                       -> if coe v18
                                                                                            then coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v19)
                                                                                                   (coe
                                                                                                      C_success_324
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                            (coe
                                                                                                               v0)))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                                            (coe
                                                                                                               v0))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                            (coe
                                                                                                               v10)
                                                                                                            (coe
                                                                                                               v11)
                                                                                                            (coe
                                                                                                               v13))
                                                                                                         (coe
                                                                                                            du_specFst_646))
                                                                                                      (coe
                                                                                                         (0 ::
                                                                                                            Integer))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                                         (coe
                                                                                                            v0)))
                                                                                            else coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v19)
                                                                                                   (coe
                                                                                                      C_failure_326
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                                         (coe
                                                                                                            ("fst"
                                                                                                             ::
                                                                                                             Data.Text.Text))))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           _ -> coe v9
                                                                    _ -> coe v9
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> coe v9
                                               _ -> coe v9)
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1776
                             -> let v7
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_inferElabV_1460 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                                (coe
                                                   MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe ("Generators" :: Data.Text.Text))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe ("snd" :: Data.Text.Text))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                                coe
                                  (case coe v7 of
                                     C_success_300 v8 v9 v10 v11 v12
                                       -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                          coe
                                            (case coe v13 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                 -> if coe v14
                                                      then coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_success_324 (coe v9) (coe v10)
                                                                (coe v11) (coe v12))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_failure_326
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                   (coe v2) (coe v8)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     C_failure_302 v8
                                       -> let v9 = coe C_failure_326 (coe v8) in
                                          coe
                                            (case coe v2 of
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                                        -> case coe v11 of
                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                                               -> case coe v15 of
                                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                                      -> case coe v16 of
                                                                           MAlonzo.Code.Once.Type.C_pure_34
                                                                             -> let v17
                                                                                      = d__'8799'T__224
                                                                                          (coe v14)
                                                                                          (coe
                                                                                             v12) in
                                                                                coe
                                                                                  (case coe v17 of
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                       -> if coe v18
                                                                                            then coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v19)
                                                                                                   (coe
                                                                                                      C_success_324
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                            (coe
                                                                                                               v0)))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                                            (coe
                                                                                                               v0))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                            (coe
                                                                                                               v10)
                                                                                                            (coe
                                                                                                               v11)
                                                                                                            (coe
                                                                                                               v14))
                                                                                                         (coe
                                                                                                            du_specSnd_656))
                                                                                                      (coe
                                                                                                         (0 ::
                                                                                                            Integer))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                                         (coe
                                                                                                            v0)))
                                                                                            else coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v19)
                                                                                                   (coe
                                                                                                      C_failure_326
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                                         (coe
                                                                                                            ("snd"
                                                                                                             ::
                                                                                                             Data.Text.Text))))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           _ -> coe v9
                                                                    _ -> coe v9
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> coe v9
                                               _ -> coe v9)
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1778
                             -> let v7
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_inferElabV_1460 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                                (coe
                                                   MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe ("Generators" :: Data.Text.Text))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe ("terminal" :: Data.Text.Text))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                                coe
                                  (case coe v7 of
                                     C_success_300 v8 v9 v10 v11 v12
                                       -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                          coe
                                            (case coe v13 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                 -> if coe v14
                                                      then coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_success_324 (coe v9) (coe v10)
                                                                (coe v11) (coe v12))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_failure_326
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                   (coe v2) (coe v8)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     C_failure_302 v8
                                       -> let v9 = coe C_failure_326 (coe v8) in
                                          coe
                                            (case coe v2 of
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                                        -> case coe v13 of
                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.Once.Type.C_pure_34
                                                                      -> case coe v12 of
                                                                           MAlonzo.Code.Once.Type.C_Unit_118
                                                                             -> coe
                                                                                  C_success_324
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                        (coe v0)))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                        (coe v0))
                                                                                     (coe v2)
                                                                                     (coe
                                                                                        du_specTerminal_700))
                                                                                  (coe
                                                                                     (0 :: Integer))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                     (coe v0))
                                                                           _ -> coe v9
                                                                    _ -> coe v9
                                                             _ -> coe v9
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> coe v9)
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1780
                             -> let v7
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_inferElabV_1460 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                                (coe
                                                   MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe ("Generators" :: Data.Text.Text))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe ("initial" :: Data.Text.Text))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                                coe
                                  (case coe v7 of
                                     C_success_300 v8 v9 v10 v11 v12
                                       -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                          coe
                                            (case coe v13 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                 -> if coe v14
                                                      then coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_success_324 (coe v9) (coe v10)
                                                                (coe v11) (coe v12))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_failure_326
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                   (coe v2) (coe v8)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     C_failure_302 v8
                                       -> let v9 = coe C_failure_326 (coe v8) in
                                          coe
                                            (case coe v2 of
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Once.Type.C_Void_120
                                                        -> case coe v11 of
                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                                               -> case coe v13 of
                                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                                      -> case coe v14 of
                                                                           MAlonzo.Code.Once.Type.C_pure_34
                                                                             -> coe
                                                                                  C_success_324
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                        (coe v0)))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                        (coe v0))
                                                                                     (coe v2)
                                                                                     (coe
                                                                                        du_specInitial_706))
                                                                                  (coe
                                                                                     (0 :: Integer))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                     (coe v0))
                                                                           _ -> coe v9
                                                                    _ -> coe v9
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> coe v9
                                               _ -> coe v9)
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1782
                             -> let v7
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_inferElabV_1460 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                                (coe
                                                   MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe ("Generators" :: Data.Text.Text))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe ("inl" :: Data.Text.Text))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                                coe
                                  (case coe v7 of
                                     C_success_300 v8 v9 v10 v11 v12
                                       -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                          coe
                                            (case coe v13 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                 -> if coe v14
                                                      then coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_success_324 (coe v9) (coe v10)
                                                                (coe v11) (coe v12))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_failure_326
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                   (coe v2) (coe v8)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     C_failure_302 v8
                                       -> let v9 = coe C_failure_326 (coe v8) in
                                          coe
                                            (case coe v2 of
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                                        -> case coe v13 of
                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.Once.Type.C_pure_34
                                                                      -> case coe v12 of
                                                                           MAlonzo.Code.Once.Type.C__'43'__124 v15 v16
                                                                             -> let v17
                                                                                      = d__'8799'T__224
                                                                                          (coe v10)
                                                                                          (coe
                                                                                             v15) in
                                                                                coe
                                                                                  (case coe v17 of
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                       -> if coe v18
                                                                                            then coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v19)
                                                                                                   (coe
                                                                                                      C_success_324
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                            (coe
                                                                                                               v0)))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                                            (coe
                                                                                                               v0))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                            (coe
                                                                                                               v10)
                                                                                                            (coe
                                                                                                               v11)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Type.C__'43'__124
                                                                                                               (coe
                                                                                                                  v10)
                                                                                                               (coe
                                                                                                                  v16)))
                                                                                                         (coe
                                                                                                            du_specInl_666))
                                                                                                      (coe
                                                                                                         (0 ::
                                                                                                            Integer))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                                         (coe
                                                                                                            v0)))
                                                                                            else coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v19)
                                                                                                   (coe
                                                                                                      C_failure_326
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                                         (coe
                                                                                                            ("inl"
                                                                                                             ::
                                                                                                             Data.Text.Text))))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           _ -> coe v9
                                                                    _ -> coe v9
                                                             _ -> coe v9
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> coe v9)
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1784
                             -> let v7
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_inferElabV_1460 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                                                (coe
                                                   MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe ("Generators" :: Data.Text.Text))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe ("inr" :: Data.Text.Text))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))) in
                                coe
                                  (case coe v7 of
                                     C_success_300 v8 v9 v10 v11 v12
                                       -> let v13 = d__'8799'T__224 (coe v2) (coe v8) in
                                          coe
                                            (case coe v13 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                 -> if coe v14
                                                      then coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_success_324 (coe v9) (coe v10)
                                                                (coe v11) (coe v12))
                                                      else coe
                                                             seq (coe v15)
                                                             (coe
                                                                C_failure_326
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                   (coe v2) (coe v8)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     C_failure_302 v8
                                       -> let v9 = coe C_failure_326 (coe v8) in
                                          coe
                                            (case coe v2 of
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                                                 -> case coe v11 of
                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                                        -> case coe v13 of
                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.Once.Type.C_pure_34
                                                                      -> case coe v12 of
                                                                           MAlonzo.Code.Once.Type.C__'43'__124 v15 v16
                                                                             -> let v17
                                                                                      = d__'8799'T__224
                                                                                          (coe v10)
                                                                                          (coe
                                                                                             v16) in
                                                                                coe
                                                                                  (case coe v17 of
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                       -> if coe v18
                                                                                            then coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v19)
                                                                                                   (coe
                                                                                                      C_success_324
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                            (coe
                                                                                                               v0)))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1254
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                                                                            (coe
                                                                                                               v0))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                            (coe
                                                                                                               v10)
                                                                                                            (coe
                                                                                                               v11)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Type.C__'43'__124
                                                                                                               (coe
                                                                                                                  v15)
                                                                                                               (coe
                                                                                                                  v10)))
                                                                                                         (coe
                                                                                                            du_specInr_676))
                                                                                                      (coe
                                                                                                         (0 ::
                                                                                                            Integer))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                                         (coe
                                                                                                            v0)))
                                                                                            else coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v19)
                                                                                                   (coe
                                                                                                      C_failure_326
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                                         (coe
                                                                                                            ("inr"
                                                                                                             ::
                                                                                                             Data.Text.Text))))
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           _ -> coe v9
                                                                    _ -> coe v9
                                                             _ -> coe v9
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> coe v9)
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1788
                             -> let v8
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_inferElabV_1460 (coe v0)
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                                (coe v1))) in
                                coe
                                  (case coe v8 of
                                     C_success_300 v9 v10 v11 v12 v13
                                       -> let v14 = d__'8799'T__224 (coe v2) (coe v9) in
                                          coe
                                            (case coe v14 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                 -> if coe v15
                                                      then coe
                                                             seq (coe v16)
                                                             (coe
                                                                C_success_324 (coe v10) (coe v11)
                                                                (coe v12) (coe v13))
                                                      else coe
                                                             seq (coe v16)
                                                             (coe
                                                                C_failure_326
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                   (coe v2) (coe v9)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     C_failure_302 v9
                                       -> let v10
                                                = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_48
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                       (coe v0))
                                                    (coe v1) in
                                          coe
                                            (case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                 -> coe
                                                      C_success_324
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Syntax.C_poly_402
                                                         v1)
                                                      (coe (0 :: Integer))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                         (coe v0))
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> coe C_failure_326 (coe v9)
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkPair
d_checkPair_1326 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPair_1326 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_326
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                    (coe ("pair" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v7
                  -> case coe v7 of
                       MAlonzo.Code.Once.CanonicalName.C_canonical_10 v8
                         -> case coe v8 of
                              (:) v9 v10
                                -> case coe v9 of
                                     l | (==) l ("Generators" :: Data.Text.Text) ->
                                         case coe v10 of
                                           (:) v11 v12
                                             -> case coe v11 of
                                                  l | (==) l ("pair" :: Data.Text.Text) ->
                                                      case coe v12 of
                                                        []
                                                          -> case coe v3 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                                                 -> case coe v14 of
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> case coe v17 of
                                                                                    MAlonzo.Code.Once.Type.C_pure_34
                                                                                      -> case coe
                                                                                                v15 of
                                                                                           MAlonzo.Code.Once.Type.C__'42'__122 v18 v19
                                                                                             -> let v20
                                                                                                      = d_checkElabV_1468
                                                                                                          (coe
                                                                                                             v0)
                                                                                                          (coe
                                                                                                             v6)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                             (coe
                                                                                                                v13)
                                                                                                             (coe
                                                                                                                v14)
                                                                                                             (coe
                                                                                                                v18)) in
                                                                                                coe
                                                                                                  (case coe
                                                                                                          v20 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                       -> case coe
                                                                                                                 v21 of
                                                                                                            C_success_324 v23 v24 v25 v26
                                                                                                              -> let v27
                                                                                                                       = d_checkElabV_1468
                                                                                                                           (coe
                                                                                                                              v0)
                                                                                                                           (coe
                                                                                                                              v2)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                              (coe
                                                                                                                                 v13)
                                                                                                                              (coe
                                                                                                                                 v14)
                                                                                                                              (coe
                                                                                                                                 v19)) in
                                                                                                                 coe
                                                                                                                   (case coe
                                                                                                                           v27 of
                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                        -> case coe
                                                                                                                                  v28 of
                                                                                                                             C_success_324 v30 v31 v32 v33
                                                                                                                               -> coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                    (coe
                                                                                                                                       C_success_324
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                                                                          (coe
                                                                                                                                             v23)
                                                                                                                                          (coe
                                                                                                                                             v30))
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_fork''_478
                                                                                                                                          v23
                                                                                                                                          v30
                                                                                                                                          v24
                                                                                                                                          v31)
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
                                                                                                                                                v32)))
                                                                                                                                       (coe
                                                                                                                                          v33))
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_480
                                                                                                                                       v23
                                                                                                                                       v30
                                                                                                                                       v22
                                                                                                                                       v29)
                                                                                                                             C_failure_326 v30
                                                                                                                               -> coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                    (coe
                                                                                                                                       v28)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                            C_failure_326 v23
                                                                                                              -> coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      v21)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> coe
                                                                                                  v4
                                                                                    MAlonzo.Code.Once.Type.C_eff_36
                                                                                      -> case coe
                                                                                                v15 of
                                                                                           MAlonzo.Code.Once.Type.C__'42'__122 v18 v19
                                                                                             -> let v20
                                                                                                      = d_checkElabV_1468
                                                                                                          (coe
                                                                                                             v0)
                                                                                                          (coe
                                                                                                             v6)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                             (coe
                                                                                                                v13)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                (coe
                                                                                                                   v16)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Once.Type.C_pure_34))
                                                                                                             (coe
                                                                                                                v18)) in
                                                                                                coe
                                                                                                  (case coe
                                                                                                          v20 of
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                                                                       -> case coe
                                                                                                                 v21 of
                                                                                                            C_success_324 v23 v24 v25 v26
                                                                                                              -> let v27
                                                                                                                       = d_checkElabV_1468
                                                                                                                           (coe
                                                                                                                              v0)
                                                                                                                           (coe
                                                                                                                              v2)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                              (coe
                                                                                                                                 v13)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                                 (coe
                                                                                                                                    v16)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Once.Type.C_pure_34))
                                                                                                                              (coe
                                                                                                                                 v19)) in
                                                                                                                 coe
                                                                                                                   (case coe
                                                                                                                           v27 of
                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                                                        -> case coe
                                                                                                                                  v28 of
                                                                                                                             C_success_324 v30 v31 v32 v33
                                                                                                                               -> coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                    (coe
                                                                                                                                       C_success_324
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                                                                          (coe
                                                                                                                                             v23)
                                                                                                                                          (coe
                                                                                                                                             v30))
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Once.Surface.Syntax.C_fork''_478
                                                                                                                                             v23
                                                                                                                                             v30
                                                                                                                                             v24
                                                                                                                                             v31))
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
                                                                                                                                                v32)))
                                                                                                                                       (coe
                                                                                                                                          v33))
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_480
                                                                                                                                          v23
                                                                                                                                          v30
                                                                                                                                          v22
                                                                                                                                          v29))
                                                                                                                             C_failure_326 v30
                                                                                                                               -> coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                    (coe
                                                                                                                                       v28)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                            C_failure_326 v23
                                                                                                              -> coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                   (coe
                                                                                                                      v21)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> coe
                                                                                                  v4
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             _ -> coe v4
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> coe v4
                                                        _ -> coe v4
                                                  _ -> coe v4
                                           _ -> coe v4
                                     _ -> coe v4
                              _ -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkPairLit
d_checkPairLit_1338 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkPairLit_1338 v0 v1 v2 v3 v4
  = let v5 = d_checkElabV_1468 (coe v0) (coe v1) (coe v3) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                C_success_324 v8 v9 v10 v11
                  -> let v12 = d_checkElabV_1468 (coe v0) (coe v2) (coe v4) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 C_success_324 v15 v16 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           C_success_324
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                              (coe v8) (coe v15))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v8 v15 v9
                                              v16)
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v10)
                                              (coe v17))
                                           (coe v18))
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_550
                                           v8 v15 v7 v14)
                                 C_failure_326 v15
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_326 v8
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCase
d_checkCase_1348 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCase_1348 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_326
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                    (coe ("case" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v7
                  -> case coe v7 of
                       MAlonzo.Code.Once.CanonicalName.C_canonical_10 v8
                         -> case coe v8 of
                              (:) v9 v10
                                -> case coe v9 of
                                     l | (==) l ("Generators" :: Data.Text.Text) ->
                                         case coe v10 of
                                           (:) v11 v12
                                             -> case coe v11 of
                                                  l | (==) l ("case" :: Data.Text.Text) ->
                                                      case coe v12 of
                                                        []
                                                          -> case coe v3 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                                                 -> case coe v13 of
                                                                      MAlonzo.Code.Once.Type.C__'43'__124 v16 v17
                                                                        -> case coe v14 of
                                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                                                               -> case coe v18 of
                                                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                                                      -> let v20
                                                                                               = d_checkCaseGo_1364
                                                                                                   (coe
                                                                                                      v0)
                                                                                                   (coe
                                                                                                      v6)
                                                                                                   (coe
                                                                                                      v2)
                                                                                                   (coe
                                                                                                      v16)
                                                                                                   (coe
                                                                                                      v17)
                                                                                                   (coe
                                                                                                      v15)
                                                                                                   (coe
                                                                                                      v19) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v19 of
                                                                                              MAlonzo.Code.Once.Type.C_eff_36
                                                                                                -> let v21
                                                                                                         = d_checkCaseGo_1364
                                                                                                             (coe
                                                                                                                v0)
                                                                                                             (coe
                                                                                                                v6)
                                                                                                             (coe
                                                                                                                v2)
                                                                                                             (coe
                                                                                                                v16)
                                                                                                             (coe
                                                                                                                v17)
                                                                                                             (coe
                                                                                                                v15)
                                                                                                             (coe
                                                                                                                v19) in
                                                                                                   coe
                                                                                                     (case coe
                                                                                                             v21 of
                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                                                                          -> case coe
                                                                                                                    v22 of
                                                                                                               C_success_324 v24 v25 v26 v27
                                                                                                                 -> coe
                                                                                                                      v21
                                                                                                               C_failure_326 v24
                                                                                                                 -> let v25
                                                                                                                          = d_checkCaseGo_1364
                                                                                                                              (coe
                                                                                                                                 v0)
                                                                                                                              (coe
                                                                                                                                 v6)
                                                                                                                              (coe
                                                                                                                                 v2)
                                                                                                                              (coe
                                                                                                                                 v16)
                                                                                                                              (coe
                                                                                                                                 v17)
                                                                                                                              (coe
                                                                                                                                 v15)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Once.Type.C_pure_34) in
                                                                                                                    coe
                                                                                                                      (case coe
                                                                                                                              v25 of
                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                                                                           -> case coe
                                                                                                                                     v26 of
                                                                                                                                C_success_324 v28 v29 v30 v31
                                                                                                                                  -> coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                       (coe
                                                                                                                                          C_success_324
                                                                                                                                          (coe
                                                                                                                                             v28)
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                                                                             v29)
                                                                                                                                          (coe
                                                                                                                                             v30)
                                                                                                                                          (coe
                                                                                                                                             v31))
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618
                                                                                                                                          v27)
                                                                                                                                C_failure_326 v28
                                                                                                                                  -> coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                       (coe
                                                                                                                                          v26)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                              _ -> coe
                                                                                                     v20)
                                                                                    _ -> coe v4
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> coe v4
                                                               _ -> coe v4
                                                        _ -> coe v4
                                                  _ -> coe v4
                                           _ -> coe v4
                                     _ -> coe v4
                              _ -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkCaseGo
d_checkCaseGo_1364 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCaseGo_1364 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = d_checkElabV_1468
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                 (coe
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6))
                 (coe v5)) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                C_success_324 v10 v11 v12 v13
                  -> let v14
                           = d_checkElabV_1468
                               (coe v0) (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v4)
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6))
                                  (coe v5)) in
                     coe
                       (case coe v14 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                            -> case coe v15 of
                                 C_success_324 v17 v18 v19 v20
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           C_success_324
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                              (coe v10) (coe v17))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_copair''_462 v10
                                              v17 v11 v18)
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v12)
                                                 (coe v19)))
                                           (coe v13))
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_462
                                           v10 v17 v9 v16)
                                 C_failure_326 v17
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_failure_326 v10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkCompose
d_checkCompose_1374 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCompose_1374 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_326
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                    (coe ("compose" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v7
                  -> case coe v7 of
                       MAlonzo.Code.Once.CanonicalName.C_canonical_10 v8
                         -> case coe v8 of
                              (:) v9 v10
                                -> case coe v9 of
                                     l | (==) l ("Generators" :: Data.Text.Text) ->
                                         case coe v10 of
                                           (:) v11 v12
                                             -> case coe v11 of
                                                  l | (==) l ("compose" :: Data.Text.Text) ->
                                                      case coe v12 of
                                                        []
                                                          -> case coe v3 of
                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                                                 -> case coe v14 of
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                                                                        -> case coe v16 of
                                                                             MAlonzo.Code.Once.Type.C_Many_10
                                                                               -> let v18
                                                                                        = coe
                                                                                            du_checkComposeGo_1390
                                                                                            (coe v0)
                                                                                            (coe v6)
                                                                                            (coe v2)
                                                                                            (coe
                                                                                               v13)
                                                                                            (coe
                                                                                               v15)
                                                                                            (coe
                                                                                               v17)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_composeMid_1000
                                                                                               (coe
                                                                                                  v0)
                                                                                               (coe
                                                                                                  v6)
                                                                                               (coe
                                                                                                  v2)
                                                                                               (coe
                                                                                                  v13)) in
                                                                                  coe
                                                                                    (case coe v17 of
                                                                                       MAlonzo.Code.Once.Type.C_eff_36
                                                                                         -> let v19
                                                                                                  = coe
                                                                                                      du_checkComposeGo_1390
                                                                                                      (coe
                                                                                                         v0)
                                                                                                      (coe
                                                                                                         v6)
                                                                                                      (coe
                                                                                                         v2)
                                                                                                      (coe
                                                                                                         v13)
                                                                                                      (coe
                                                                                                         v15)
                                                                                                      (coe
                                                                                                         v17)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_composeMid_1000
                                                                                                         (coe
                                                                                                            v0)
                                                                                                         (coe
                                                                                                            v6)
                                                                                                         (coe
                                                                                                            v2)
                                                                                                         (coe
                                                                                                            v13)) in
                                                                                            coe
                                                                                              (case coe
                                                                                                      v19 of
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                   -> case coe
                                                                                                             v20 of
                                                                                                        C_success_324 v22 v23 v24 v25
                                                                                                          -> coe
                                                                                                               v19
                                                                                                        C_failure_326 v22
                                                                                                          -> let v23
                                                                                                                   = coe
                                                                                                                       du_checkComposeGo_1390
                                                                                                                       (coe
                                                                                                                          v0)
                                                                                                                       (coe
                                                                                                                          v6)
                                                                                                                       (coe
                                                                                                                          v2)
                                                                                                                       (coe
                                                                                                                          v13)
                                                                                                                       (coe
                                                                                                                          v15)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Once.Type.C_pure_34)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Once.TypeCheck.Classify.d_composeMid_1000
                                                                                                                          (coe
                                                                                                                             v0)
                                                                                                                          (coe
                                                                                                                             v6)
                                                                                                                          (coe
                                                                                                                             v2)
                                                                                                                          (coe
                                                                                                                             v13)) in
                                                                                                             coe
                                                                                                               (case coe
                                                                                                                       v23 of
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                                                    -> case coe
                                                                                                                              v24 of
                                                                                                                         C_success_324 v26 v27 v28 v29
                                                                                                                           -> coe
                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                (coe
                                                                                                                                   C_success_324
                                                                                                                                   (coe
                                                                                                                                      v26)
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                                                                      v27)
                                                                                                                                   (coe
                                                                                                                                      v28)
                                                                                                                                   (coe
                                                                                                                                      v29))
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618
                                                                                                                                   v25)
                                                                                                                         C_failure_326 v26
                                                                                                                           -> coe
                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                (coe
                                                                                                                                   v24)
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                       _ -> coe v18)
                                                                             _ -> coe v4
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> coe v4
                                                        _ -> coe v4
                                                  _ -> coe v4
                                           _ -> coe v4
                                     _ -> coe v4
                              _ -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4
         _ -> coe v4)
-- Once.TypeCheck.Elaborate.checkComposeGo
d_checkComposeGo_1390 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkComposeGo_1390 v0 v1 v2 v3 v4 v5 v6 ~v7
  = du_checkComposeGo_1390 v0 v1 v2 v3 v4 v5 v6
du_checkComposeGo_1390 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkComposeGo_1390 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> let v8
                 = d_checkElabV_1468
                     (coe v0) (coe v2)
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                        (coe
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                        (coe v7)) in
           coe
             (case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> case coe v9 of
                       C_success_324 v11 v12 v13 v14
                         -> let v15
                                  = d_checkElabV_1468
                                      (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                                         (coe v4)) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> case coe v16 of
                                        C_success_324 v18 v19 v20 v21
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_success_324
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                     (coe v18) (coe v11))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_comp''_444
                                                     v18 v11 v7 v19 v12)
                                                  (coe
                                                     addInt (coe (1 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                        (coe v20) (coe v13)))
                                                  (coe v21))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check_442
                                                  v7 v18 v11 v17 v10)
                                        C_failure_326 v18
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_failure_326 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_326
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("compose" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCurry
d_checkCurry_1398 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCurry_1398 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_326
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                    (coe ("curry" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
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
                                                                     = d_checkElabV_1468
                                                                         (coe v0) (coe v1)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C__'42'__122
                                                                               (coe v4) (coe v9))
                                                                            (coe v10) (coe v11)) in
                                                               coe
                                                                 (case coe v14 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                      -> case coe v15 of
                                                                           C_success_324 v17 v18 v19 v20
                                                                             -> coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     C_success_324
                                                                                     (coe v17)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_curry''_492
                                                                                        v18)
                                                                                     (coe
                                                                                        addInt
                                                                                        (coe
                                                                                           (1 ::
                                                                                              Integer))
                                                                                        (coe v19))
                                                                                     (coe v20))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_494
                                                                                     v16)
                                                                           C_failure_326 v17
                                                                             -> coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe v15)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> coe v3
                                                   _ -> coe v3
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v3
                              MAlonzo.Code.Once.Type.C_eff_36
                                -> case coe v6 of
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
                                       -> case coe v10 of
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v12 v13
                                              -> case coe v12 of
                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                     -> case coe v13 of
                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                            -> let v14
                                                                     = d_checkElabV_1468
                                                                         (coe v0) (coe v1)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C__'42'__122
                                                                               (coe v4) (coe v9))
                                                                            (coe v10) (coe v11)) in
                                                               coe
                                                                 (case coe v14 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                      -> case coe v15 of
                                                                           C_success_324 v17 v18 v19 v20
                                                                             -> coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     C_success_324
                                                                                     (coe v17)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Syntax.C_curry''_492
                                                                                           v18))
                                                                                     (coe
                                                                                        addInt
                                                                                        (coe
                                                                                           (1 ::
                                                                                              Integer))
                                                                                        (coe v19))
                                                                                     (coe v20))
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_494
                                                                                        v16))
                                                                           C_failure_326 v17
                                                                             -> coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe v15)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          _ -> coe v3
                                                   _ -> coe v3
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> coe v3
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v3
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkApply
d_checkApply_1406 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkApply_1406 v0 v1 v2
  = let v3 = d_inferElabV_1460 (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                C_success_300 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C_Unit_118
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_326
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Void_120
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_326
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C__'42'__122 v11 v12
                         -> case coe v11 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_326
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_326
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_326
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_326
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Type.C_Zero_6
                                              -> coe
                                                   seq (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_326
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                            (coe ("apply" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            MAlonzo.Code.Once.Type.C_One_8
                                              -> coe
                                                   seq (coe v17)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_326
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                            (coe ("apply" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            MAlonzo.Code.Once.Type.C_Many_10
                                              -> case coe v17 of
                                                   MAlonzo.Code.Once.Type.C_pure_34
                                                     -> let v18
                                                              = d__'8799'T__224
                                                                  (coe v13) (coe v12) in
                                                        coe
                                                          (let v19
                                                                 = d__'8799'T__224
                                                                     (coe v2) (coe v15) in
                                                           coe
                                                             (case coe v18 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                  -> if coe v20
                                                                       then coe
                                                                              seq (coe v21)
                                                                              (case coe v19 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                   -> if coe v22
                                                                                        then coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v23)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     C_success_324
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                              (coe
                                                                                                                 v0)))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                                           (coe
                                                                                                              v16)
                                                                                                           (coe
                                                                                                              v7)))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426
                                                                                                        v7
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.Type.C__'42'__122
                                                                                                           (coe
                                                                                                              v11)
                                                                                                           (coe
                                                                                                              v13))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.IR.C_apply_92)
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
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_572
                                                                                                     v13
                                                                                                     v7
                                                                                                     v5))
                                                                                        else coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v23)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     C_failure_326
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                                                        (coe
                                                                                                           v2)
                                                                                                        (coe
                                                                                                           v15)))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       else coe
                                                                              seq (coe v21)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    C_failure_326
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                       (coe
                                                                                          ("apply"
                                                                                           ::
                                                                                           Data.Text.Text))))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                   MAlonzo.Code.Once.Type.C_eff_36
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_326
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                (coe ("apply" :: Data.Text.Text))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_326
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_326
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_326
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_326
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_326
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_326
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_326
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_326
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_μ'45'type_128 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_326
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_ν'45'type_130 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_326
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Int_132
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_326
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Float_134
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_326
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Str_136
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_326
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       MAlonzo.Code.Once.Type.C_Buffer_138
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_326
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                    (coe ("apply" :: Data.Text.Text))))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                C_failure_302 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe C_failure_326 (coe v6))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkIn
d_checkIn_1414 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkIn_1414 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_326
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                    (coe ("In" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Type.C_μ'45'type_128 v4
           -> coe
                du_checkInGo_1424 (coe v0) (coe v1) (coe v4)
                (coe
                   MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224 (coe v4))
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkInGo
d_checkInGo_1424 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkInGo_1424 v0 v1 v2 v3 ~v4 = du_checkInGo_1424 v0 v1 v2 v3
du_checkInGo_1424 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkInGo_1424 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = d_checkElabV_1468
                     (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v2)
                        (coe MAlonzo.Code.Once.Type.C_μ'45'type_128 (coe v2))) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_324 v8 v9 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_324
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v8
                                    (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                       (coe v2)
                                       (coe MAlonzo.Code.Once.Type.C_μ'45'type_128 (coe v2)))
                                    (coe
                                       MAlonzo.Code.Once.IR.C_In_96
                                       (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                          (coe v2) (coe v4))
                                       (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                    v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_560
                                 v8 v4 v7)
                       C_failure_326 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_326
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkCata
d_checkCata_1432 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCata_1432 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 C_failure_326
                 (coe
                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                    (coe ("cata" :: Data.Text.Text))))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
           -> case coe v4 of
                MAlonzo.Code.Once.Type.C_μ'45'type_128 v7
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v8 v9
                         -> case coe v8 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> let v10
                                         = coe
                                             du_checkCataGo_1446 (coe v0) (coe v1) (coe v7) (coe v6)
                                             (coe v9)
                                             (coe
                                                MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                                (coe v7)) in
                                   coe
                                     (case coe v9 of
                                        MAlonzo.Code.Once.Type.C_eff_36
                                          -> let v11
                                                   = coe
                                                       du_checkCataGo_1446 (coe v0) (coe v1)
                                                       (coe v7) (coe v6) (coe v9)
                                                       (coe
                                                          MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                                          (coe v7)) in
                                             coe
                                               (case coe v11 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                    -> case coe v12 of
                                                         C_success_324 v14 v15 v16 v17 -> coe v11
                                                         C_failure_326 v14
                                                           -> let v15
                                                                    = coe
                                                                        du_checkCataGo_1446 (coe v0)
                                                                        (coe v1) (coe v7) (coe v6)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_pure_34)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                                                           (coe v7)) in
                                                              coe
                                                                (case coe v15 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                     -> case coe v16 of
                                                                          C_success_324 v18 v19 v20 v21
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    C_success_324
                                                                                    (coe v18)
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                       v19)
                                                                                    (coe v20)
                                                                                    (coe v21))
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618
                                                                                    v17)
                                                                          C_failure_326 v18
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe v16)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> coe v10)
                              _ -> coe v3
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v3
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.checkCataGo
d_checkCataGo_1446 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkCataGo_1446 v0 v1 v2 v3 v4 v5 ~v6
  = du_checkCataGo_1446 v0 v1 v2 v3 v4 v5
du_checkCataGo_1446 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkCataGo_1446 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> let v7
                 = d_checkElabV_1468
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364 (coe v0)))
                     (coe v1)
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                        (coe
                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v2) (coe v3))
                        (coe
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                        (coe v3)) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> case coe v8 of
                       C_success_324 v10 v11 v12 v13
                         -> coe
                              seq (coe v10)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    C_success_324
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                                    (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_504 v6 v11)
                                    (coe addInt (coe (1 :: Integer)) (coe v12))
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                       (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_506 v6
                                    v9))
                       C_failure_326 v10
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_326
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElab-RApp-other
d_inferElab'45'RApp'45'other_1454 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_InferElabResult_286
d_inferElab'45'RApp'45'other_1454 v0 v1 v2
  = let v3
          = coe
              du_asFun_1036
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe d_inferElabV_1460 (coe v0) (coe v1))) in
    coe
      (case coe v3 of
         C_isFun_1020 v4 v5 v6 v7 v8 v9 v10
           -> let v11
                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_checkElabV_1468 (coe v0) (coe v2) (coe v4)) in
              coe
                (case coe v11 of
                   C_success_324 v12 v13 v14 v15
                     -> coe
                          C_success_300 (coe v6)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v7)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v5)
                                (coe v12)))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_app_48 v7 v12 v4 v5 v8 v13)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v9) (coe v14))
                          (coe v15)
                   C_failure_326 v12 -> coe C_failure_302 (coe v12)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_isEff_1028 v4 v5 v6 v7 v8 v9
           -> let v10
                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe d_checkElabV_1468 (coe v0) (coe v2) (coe v4)) in
              coe
                (case coe v10 of
                   C_success_324 v11 v12 v13 v14
                     -> coe
                          C_success_300
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_eff_36))
                             (coe v5))
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v6)
                             (coe v11))
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v6 v11 v4 v7 v12)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v8) (coe v13))
                          (coe v14)
                   C_failure_326 v11 -> coe C_failure_302 (coe v11)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         C_notFun_1030 v4 -> coe C_failure_302 (coe v4)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV
d_inferElabV_1460 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV_1460 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v2
        -> coe
             du_inferElabV'45'RVar'45'lookup'45'aux_1762 (coe v0) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_572 (coe v0)
                (coe v2))
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v2 v3
        -> coe
             du_inferElabV'45'RQualified'45'aux_1684 (coe v0) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("." :: Data.Text.Text) v2)))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v2
        -> coe
             d_inferElabV'45'RResolved'45'dispatch_1924 (coe v0) (coe v2)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_1510 (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v2 v3
        -> coe
             du_inferElabV'45'RApp'45'dispatch_1794 (coe v0) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_1164
                (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_LambdaInInferMode_24))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v2 v3 v4
        -> coe
             du_inferElabV'45'RLet'45'aux_1568 (coe v0) (coe v2) (coe v4)
             (coe d_inferElabV_1460 (coe v0) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v2 v3
        -> coe
             du_inferElabV'45'RPair'45'aux_1492
             (coe d_inferElabV_1460 (coe v0) (coe v2))
             (coe d_inferElabV_1460 (coe v0) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v2 v3 v4 v5 v6
        -> coe
             du_inferElabV'45'RDestruct'45'aux_1604 (coe v0) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe d_inferElabV_1460 (coe v0) (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_300 (coe MAlonzo.Code.Once.Type.C_Unit_118)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_44)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_300 (coe MAlonzo.Code.Once.Type.C_Int_132)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_int_184 v2)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_22)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v2 v3 v4 v5
        -> coe
             du_inferElabV'45'RFloat'45'aux_1974 (coe v0) (coe v2) (coe v3)
             (coe v4)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_300 (coe MAlonzo.Code.Once.Type.C_Str_136)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_str_190 v2)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_40)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v2 v3
        -> coe
             du_inferElabV'45'RAnnot'45'aux_1500 (coe v3)
             (coe d_checkElabV_1468 (coe v0) (coe v2) (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v2 v3 v4
        -> coe
             du_inferElabV'45'RBinOp'45'aux_1558 (coe v2)
             (coe d_inferElabV_1460 (coe v0) (coe v3))
             (coe d_inferElabV_1460 (coe v0) (coe v4))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v3
        -> coe d_inferElabV'45'neg'45'dispatch_1512 (coe v0) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("ana" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV
d_checkElabV_1468 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV_1468 v0 v1 v2
  = coe du_checkElabV'45'wf_1476 (coe v0) (coe v1) (coe v2)
-- Once.TypeCheck.Elaborate.checkElabV-wf
d_checkElabV'45'wf_1476 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'wf_1476 v0 ~v1 v2 v3
  = du_checkElabV'45'wf_1476 v0 v2 v3
du_checkElabV'45'wf_1476 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'wf_1476 v0 v1 v2
  = let v3
          = coe
              du_embedOrSubsume_568 (coe v2)
              (coe d_inferElabV_1460 (coe v0) (coe v1)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
           -> let v5
                    = coe
                        du_inferElabV'45'RVar'45'lookup'45'aux_1762 (coe v0) (coe v4)
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_572 (coe v0)
                           (coe v4))
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                           (coe v4)) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v6 of
                          C_success_300 v8 v9 v10 v11 v12
                            -> coe du_embedOrSubsume_568 (coe v2) (coe v5)
                          C_failure_302 v8
                            -> coe
                                 d_checkElabV'45'RVar'45'bbc'45'other'45'aux_1940 (coe v0) (coe v4)
                                 (coe v2) (coe v5)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v4
           -> coe
                du_checkElabV'45'RResolved'45'dispatch_1932 (coe v0) (coe v2)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyGen_1510 (coe v4))
                (coe d_inferElabV_1460 (coe v0) (coe v1))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v4 v5
           -> coe
                du_checkElabV'45'RApp'45'dispatch_1806 (coe v0) (coe v4) (coe v5)
                (coe v2)
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_1164
                   (coe v4))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v4 v5
           -> let v6
                    = coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           C_failure_326
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Error.C_LambdaRequiresFunctionType_26))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) in
              coe
                (case coe v2 of
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v7 v8 v9
                     -> case coe v8 of
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50 v10 v11
                            -> case coe v11 of
                                 MAlonzo.Code.Once.Type.C_pure_34
                                   -> let v12
                                            = d_checkElabV_1468
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                                   (coe v0) (coe v4) (coe v7))
                                                (coe v5) (coe v9) in
                                      coe
                                        (case coe v12 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                             -> case coe v13 of
                                                  C_success_324 v15 v16 v17 v18
                                                    -> case coe v15 of
                                                         MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v20 v21
                                                           -> let v22
                                                                    = d_decideLeq_1178
                                                                        (coe v20) (coe v10) in
                                                              coe
                                                                (case coe v22 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe
                                                                             C_success_324 (coe v21)
                                                                             (coe
                                                                                MAlonzo.Code.Once.Surface.Syntax.C_lam_32
                                                                                v20 v16)
                                                                             (coe
                                                                                addInt
                                                                                (coe (1 :: Integer))
                                                                                (coe v17))
                                                                             (coe v18))
                                                                          (coe
                                                                             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_534
                                                                             v20 v14)
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe
                                                                             C_failure_326
                                                                             (coe
                                                                                MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_72
                                                                                (coe v4) (coe v10)
                                                                                (coe v20)))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  C_failure_326 v15
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v13)
                                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 MAlonzo.Code.Once.Type.C_eff_36
                                   -> case coe v10 of
                                        MAlonzo.Code.Once.Type.C_Many_10
                                          -> let v12
                                                   = d_checkElabV_1468
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                                          (coe v0) (coe v4) (coe v7))
                                                       (coe v5) (coe v9) in
                                             coe
                                               (case coe v12 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                    -> case coe v13 of
                                                         C_success_324 v15 v16 v17 v18
                                                           -> case coe v15 of
                                                                MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v20 v21
                                                                  -> let v22
                                                                           = d_decideLeq_1178
                                                                               (coe v20)
                                                                               (coe v10) in
                                                                     coe
                                                                       (case coe v22 of
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    C_success_324
                                                                                    (coe v21)
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_lam_32
                                                                                          v20 v16))
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe v17))
                                                                                    (coe v18))
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_534
                                                                                       v20 v14))
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    C_failure_326
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_UsageViolation_72
                                                                                       (coe v4)
                                                                                       (coe v10)
                                                                                       (coe v20)))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         C_failure_326 v15
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v13)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> coe v6
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> coe v6)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v4 v5
           -> coe
                d_checkElabV'45'RPair'45'aux_1984 (coe v0) (coe v4) (coe v5)
                (coe v2) (coe d_classifyRPairTarget_198 (coe v2))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4
           -> coe d_checkElabV'45'RInt'45'aux_1948 (coe v0) (coe v4) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v4 v5 v6 v7
           -> coe
                du_checkElabV'45'RFloat'45'aux_1962 (coe v0) (coe v4) (coe v5)
                (coe v6) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v5
           -> coe
                d_checkElabV'45'neg'45'dispatch_1526 (coe v0) (coe v5) (coe v2)
                (coe d_negOperandView_350 (coe v5))
         _ -> coe v3)
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other
d_inferElabV'45'RApp'45'other_1484 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'other_1484 v0 v1 v2
  = coe
      du_inferElabV'45'RApp'45'other'45'aux_1784 (coe v0) (coe v1)
      (coe v2)
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHead_1370
         (coe v1))
-- Once.TypeCheck.Elaborate.inferElabV-RPair-aux
d_inferElabV'45'RPair'45'aux_1492 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RPair'45'aux_1492 ~v0 ~v1 ~v2 v3 v4
  = du_inferElabV'45'RPair'45'aux_1492 v3 v4
du_inferElabV'45'RPair'45'aux_1492 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RPair'45'aux_1492 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_300 v4 v5 v6 v7 v8
               -> case coe v1 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> case coe v9 of
                           C_success_300 v11 v12 v13 v14 v15
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_300
                                     (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v4) (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                        (coe v5) (coe v12))
                                     (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v5 v12 v6 v13)
                                     (coe
                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v7)
                                        (coe v14))
                                     (coe v15))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_128 v5 v12 v3
                                     v10)
                           C_failure_302 v11
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_302 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RAnnot-aux
d_inferElabV'45'RAnnot'45'aux_1500 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RAnnot'45'aux_1500 ~v0 ~v1 v2 v3
  = du_inferElabV'45'RAnnot'45'aux_1500 v2 v3
du_inferElabV'45'RAnnot'45'aux_1500 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RAnnot'45'aux_1500 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v2 of
             C_success_324 v4 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_success_300 (coe v0) (coe v4) (coe v5) (coe v6) (coe v7))
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_112 v3)
             C_failure_326 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_302 (coe v4))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RUnaryOp-aux
d_inferElabV'45'RUnaryOp'45'aux_1506 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RUnaryOp'45'aux_1506 ~v0 ~v1 v2
  = du_inferElabV'45'RUnaryOp'45'aux_1506 v2
du_inferElabV'45'RUnaryOp'45'aux_1506 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RUnaryOp'45'aux_1506 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             C_success_300 v3 v4 v5 v6 v7
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_Unit_118
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Void_120
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'42'__122 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v8 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_ν'45'type_130 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Int_132
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_300 (coe v3) (coe v4)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v5)
                              (coe addInt (coe (1 :: Integer)) (coe v6)) (coe v7))
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136 v2)
                    MAlonzo.Code.Once.Type.C_Float_134
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Str_136
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Buffer_138
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_302 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-neg-dispatch
d_inferElabV'45'neg'45'dispatch_1512 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'neg'45'dispatch_1512 v0 v1
  = coe
      d_inferElabV'45'neg'45'aux_1518 (coe v0) (coe v1)
      (coe d_negOperandView_350 (coe v1))
-- Once.TypeCheck.Elaborate.inferElabV-neg-aux
d_inferElabV'45'neg'45'aux_1518 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_NegOperandView_328 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'neg'45'aux_1518 v0 v1 v2
  = case coe v2 of
      C_nov'45'int_332
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_300 (coe MAlonzo.Code.Once.Type.C_Int_132)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_int_184
                          (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v4)))
                       (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_22))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_342
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v7 v8 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_300 (coe MAlonzo.Code.Once.Type.C_Float_134)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_float_198
                          (MAlonzo.Code.Once.Float.Decimal.d_negate_22
                             (coe
                                MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v7) (coe v8)
                                (coe v9))))
                       (coe (1 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_148)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_346
        -> coe
             du_inferElabV'45'RUnaryOp'45'aux_1506
             (coe d_inferElabV_1460 (coe v0) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-dispatch
d_checkElabV'45'neg'45'dispatch_1526 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_NegOperandView_328 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'dispatch_1526 v0 v1 v2 v3
  = case coe v3 of
      C_nov'45'int_332
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v5
               -> coe
                    d_checkElabV'45'neg'45'int'45'aux_1534 (coe v0) (coe v5) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'float_342
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v8 v9 v10 v11
               -> coe
                    du_checkElabV'45'neg'45'float'45'aux_1548 (coe v0) (coe v8)
                    (coe v9) (coe v10) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nov'45'other_346
        -> coe
             du_embedOrSubsume_568 (coe v2)
             (coe
                du_inferElabV'45'RUnaryOp'45'aux_1506
                (coe d_inferElabV_1460 (coe v0) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-neg-int-aux
d_checkElabV'45'neg'45'int'45'aux_1534 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'int'45'aux_1534 v0 v1 v2
  = let v3
          = d__'8799'T__224
              (coe v2) (coe MAlonzo.Code.Once.Type.C_Int_132) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_success_324
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_int_184
                                (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v1)))
                             (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136
                                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_22))))
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_326
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60 (coe v2)
                                (coe MAlonzo.Code.Once.Type.C_Int_132)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.checkElabV-neg-float-aux
d_checkElabV'45'neg'45'float'45'aux_1548 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'neg'45'float'45'aux_1548 v0 v1 v2 v3 ~v4 v5
  = du_checkElabV'45'neg'45'float'45'aux_1548 v0 v1 v2 v3 v5
du_checkElabV'45'neg'45'float'45'aux_1548 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'neg'45'float'45'aux_1548 v0 v1 v2 v3 v4
  = let v5
          = d__'8799'T__224
              (coe v4) (coe MAlonzo.Code.Once.Type.C_Float_134) in
    coe
      (case coe v5 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
           -> if coe v6
                then coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_success_324
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_float_198
                                (MAlonzo.Code.Once.Float.Decimal.d_negate_22
                                   (coe
                                      MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v1)
                                      (coe v2) (coe v3))))
                             (coe (1 :: Integer))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_148)))
                else coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_326
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60 (coe v4)
                                (coe MAlonzo.Code.Once.Type.C_Float_134)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RBinOp-aux
d_inferElabV'45'RBinOp'45'aux_1558 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RBinOp'45'aux_1558 ~v0 v1 ~v2 ~v3 v4 v5
  = du_inferElabV'45'RBinOp'45'aux_1558 v1 v4 v5
du_inferElabV'45'RBinOp'45'aux_1558 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RBinOp'45'aux_1558 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_300 v5 v6 v7 v8 v9
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_Unit_118
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Void_120
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'42'__122 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_ν'45'type_130 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Int_132
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v10 of
                                  C_success_300 v12 v13 v14 v15 v16
                                    -> case coe v12 of
                                         MAlonzo.Code.Once.Type.C_Unit_118
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Void_120
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'42'__122 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_μ'45'type_128 v17
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_ν'45'type_130 v17
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Int_132
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_add_208
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_sub_218
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_mul_228
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_div_286
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_mod''_296
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_lt_314
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_le_324
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_gt_334
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_ge_344
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_eq_354
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'43'__124
                                                             (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_Unit_118))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_ne_364
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268
                                                          v6 v13 v4 v11)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_Float_134
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_238
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_248
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_258
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268
                                                             v6 v13
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v7)
                                                             v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_Str_136
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Buffer_138
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  C_failure_302 v12
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            C_failure_302
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                               (coe v12)))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Type.C_Float_134
                      -> case coe v2 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> case coe v10 of
                                  C_success_300 v12 v13 v14 v15 v16
                                    -> case coe v12 of
                                         MAlonzo.Code.Once.Type.C_Unit_118
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Void_120
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'42'__122 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_μ'45'type_128 v17
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_ν'45'type_130 v17
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Int_132
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_238
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_248
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_258
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v5)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268
                                                             v6 v13 v7
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                                v14))
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe v5) (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_Float_134
                                           -> case coe v0 of
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fadd_238
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fsub_248
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fmul_258
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_success_300 (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                             (coe v6) (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268
                                                             v6 v13 v7 v14)
                                                          (coe
                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                             (coe v8) (coe v15))
                                                          (coe v16))
                                                       (coe
                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226
                                                          v6 v13 v4 v11)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          C_failure_302
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Int_132)
                                                                (coe v12))))
                                                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Once.Type.C_Str_136
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         MAlonzo.Code.Once.Type.C_Buffer_138
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   C_failure_302
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                         (coe v5) (coe v12))))
                                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  C_failure_302 v12
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            C_failure_302
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Error.C_BinOpRightError_80
                                               (coe v12)))
                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Once.Type.C_Str_136
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Buffer_138
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                    (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v5))))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_302 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_302
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_BinOpLeftError_78 (coe v5)))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux
d_inferElabV'45'RLet'45'aux_1568 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RLet'45'aux_1568 v0 v1 ~v2 v3 v4
  = du_inferElabV'45'RLet'45'aux_1568 v0 v1 v3 v4
du_inferElabV'45'RLet'45'aux_1568 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RLet'45'aux_1568 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_300 v6 v7 v8 v9 v10
               -> coe
                    du_inferElabV'45'RLet'45'aux2_1590 (coe v6) (coe v7) (coe v8)
                    (coe v9) (coe v5)
                    (coe
                       d_inferElabV_1460
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                          (coe v1) (coe v6))
                       (coe v2))
             C_failure_302 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RLet-aux2
d_inferElabV'45'RLet'45'aux2_1590 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RLet'45'aux2_1590 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8
                                  v9 v10
  = du_inferElabV'45'RLet'45'aux2_1590 v4 v5 v6 v7 v9 v10
du_inferElabV'45'RLet'45'aux2_1590 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RLet'45'aux2_1590 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             C_success_300 v8 v9 v10 v11 v12
               -> case coe v9 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_300 (coe v8)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v14)
                                    (coe v1)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v1 v15 v14 v0 v2 v10)
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3)
                                 (coe addInt (coe (1 :: Integer)) (coe v11)))
                              (coe v12))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_168 v0 v14 v1 v15
                              v4 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_302 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-aux
d_inferElabV'45'RDestruct'45'aux_1604 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'aux_1604 v0 ~v1 v2 v3 v4 v5 v6
  = du_inferElabV'45'RDestruct'45'aux_1604 v0 v2 v3 v4 v5 v6
du_inferElabV'45'RDestruct'45'aux_1604 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'aux_1604 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v6 of
             C_success_300 v8 v9 v10 v11 v12
               -> case coe v8 of
                    MAlonzo.Code.Once.Type.C_Unit_118
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Void_120
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                      -> coe
                           du_inferElabV'45'RDestruct'45'auxL_1632 (coe v0) (coe v3) (coe v4)
                           (coe v13) (coe v14) (coe v9) (coe v10) (coe v11) (coe v7)
                           (coe
                              d_inferElabV_1460
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                                 (coe v1) (coe v13))
                              (coe v2))
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_ν'45'type_130 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Int_132
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Float_134
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Str_136
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Buffer_138
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_302
                              (coe MAlonzo.Code.Once.TypeCheck.Error.C_CaseScrutineeNotSum_46))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_302 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxL
d_inferElabV'45'RDestruct'45'auxL_1632 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'auxL_1632 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
                                       v8 v9 v10 ~v11 v12 v13
  = du_inferElabV'45'RDestruct'45'auxL_1632
      v0 v4 v5 v6 v7 v8 v9 v10 v12 v13
du_inferElabV'45'RDestruct'45'auxL_1632 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'auxL_1632 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
        -> case coe v10 of
             C_success_300 v12 v13 v14 v15 v16
               -> case coe v13 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v18 v19
                      -> coe
                           du_inferElabV'45'RDestruct'45'auxR_1674 (coe v3) (coe v4) (coe v5)
                           (coe v6) (coe v7) (coe v8) (coe v12) (coe v18) (coe v19) (coe v14)
                           (coe v15) (coe v11)
                           (coe
                              d_inferElabV_1460
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                                 (coe v1) (coe v4))
                              (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_302 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RDestruct-auxR
d_inferElabV'45'RDestruct'45'auxR_1674 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RDestruct'45'auxR_1674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
                                       v7 v8 v9 v10 ~v11 v12 v13 v14 v15 v16 v17 ~v18 v19 v20
  = du_inferElabV'45'RDestruct'45'auxR_1674
      v6 v7 v8 v9 v10 v12 v13 v14 v15 v16 v17 v19 v20
du_inferElabV'45'RDestruct'45'auxR_1674 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RDestruct'45'auxR_1674 v0 v1 v2 v3 v4 v5 v6 v7 v8
                                        v9 v10 v11 v12
  = case coe v12 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
        -> case coe v13 of
             C_success_300 v15 v16 v17 v18 v19
               -> case coe v16 of
                    MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v21 v22
                      -> let v23 = d__'8799'T__224 (coe v6) (coe v15) in
                         coe
                           (case coe v23 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                -> if coe v24
                                     then coe
                                            seq (coe v25)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_success_300 (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                     (coe v2)
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                                        (coe v8) (coe v22)))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_case''_146
                                                     v2 v8 v22 v7 v21 v0 v1 v3 v9 v17)
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                        (coe v4)
                                                        (coe addInt (coe (1 :: Integer)) (coe v10)))
                                                     (coe addInt (coe (1 :: Integer)) (coe v18)))
                                                  (coe v19))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_198
                                                  v0 v1 v7 v21 v2 v8 v22 v5 v11 v14))
                                     else coe
                                            seq (coe v25)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_failure_302
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Error.C_CaseBranchMismatch_48))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_failure_302 v15
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RQualified-aux
d_inferElabV'45'RQualified'45'aux_1684 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RQualified'45'aux_1684 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RQualified'45'aux_1684 v0 v1 v2 v3
du_inferElabV'45'RQualified'45'aux_1684 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RQualified'45'aux_1684 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = coe
                     du_inferElabV'45'RQualified'45'value'45'aux_1738 (coe v0) (coe v1)
                     (coe v2) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v9 v10
                         -> case coe v9 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> coe
                                     du_inferElabV'45'RQualified'45'arrow'45'aux_1710 (coe v0)
                                     (coe v1) (coe v2) (coe v6) (coe v8) (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                                        (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52
                                        (coe v8))
                              _ -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundQualified_14 (coe v1)
                   (coe v2)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-aux
d_inferElabV'45'RResolved'45'aux_1692 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'aux_1692 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RResolved'45'aux_1692 v0 v1 v2 v3
du_inferElabV'45'RResolved'45'aux_1692 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'aux_1692 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> let v5
                 = coe
                     du_inferElabV'45'RResolved'45'value'45'aux_1748 (coe v0) (coe v1)
                     (coe v2) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v9 v10
                         -> case coe v9 of
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> coe
                                     du_inferElabV'45'RResolved'45'arrow'45'aux_1726 (coe v0)
                                     (coe v1) (coe v2) (coe v6) (coe v8) (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63'_8
                                        (coe v6))
                                     (coe
                                        MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52
                                        (coe v8))
                              _ -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe
                      MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RQualified-arrow-aux
d_inferElabV'45'RQualified'45'arrow'45'aux_1710 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RQualified'45'arrow'45'aux_1710 v0 v1 v2 v3 v4 v5
                                                ~v6 v7 ~v8 v9 ~v10
  = du_inferElabV'45'RQualified'45'arrow'45'aux_1710
      v0 v1 v2 v3 v4 v5 v7 v9
du_inferElabV'45'RQualified'45'arrow'45'aux_1710 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RQualified'45'arrow'45'aux_1710 v0 v1 v2 v3 v4 v5
                                                 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_300
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                          (coe
                             MAlonzo.Code.Once.IR.C_SigOp_156 (coe v3) (coe v4)
                             (coe
                                d_ext'45'arrow'45'info_1994 (coe v3) (coe v4) (coe v0) (coe v2)
                                (coe v1) (coe v5) (coe v8) (coe v9))))
                       (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_70
                       (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v8 v9))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_302
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                          (coe
                             MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                             (coe
                                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                ("." :: Data.Text.Text) v1))
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                             (coe v4))))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))
                   (coe
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                      (coe v4))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-arrow-aux
d_inferElabV'45'RResolved'45'arrow'45'aux_1726 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'arrow'45'aux_1726 v0 v1 v2 v3 v4 v5
                                               ~v6 v7 ~v8 v9 ~v10
  = du_inferElabV'45'RResolved'45'arrow'45'aux_1726
      v0 v1 v2 v3 v4 v5 v7 v9
du_inferElabV'45'RResolved'45'arrow'45'aux_1726 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'arrow'45'aux_1726 v0 v1 v2 v3 v4 v5
                                                v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_success_300
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                          (coe v4))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                          (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                          (coe
                             MAlonzo.Code.Once.IR.C_SigOp_156 (coe v3) (coe v4)
                             (coe
                                d_ext'45'resolved'45'info_2006 (coe v3) (coe v4) (coe v0) (coe v1)
                                (coe v5) (coe v8) (coe v9))))
                       (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v2
                       (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v8 v9))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_302
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                          (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                             (coe v4))))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))
                   (coe
                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v3)
                      (coe
                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                      (coe v4))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RQualified-value-aux
d_inferElabV'45'RQualified'45'value'45'aux_1738 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RQualified'45'value'45'aux_1738 v0 v1 v2 v3 ~v4 v5
                                                ~v6
  = du_inferElabV'45'RQualified'45'value'45'aux_1738 v0 v1 v2 v3 v5
du_inferElabV'45'RQualified'45'value'45'aux_1738 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RQualified'45'value'45'aux_1738 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_300 (coe v3)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                (coe
                   MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                   (MAlonzo.Code.Once.CanonicalName.d_bare_12
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            ("." :: Data.Text.Text) v1)))
                   v5)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
             (coe
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_70 v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))
                   (coe v3)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-value-aux
d_inferElabV'45'RResolved'45'value'45'aux_1748 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'value'45'aux_1748 v0 v1 v2 v3 ~v4 v5
                                               ~v6
  = du_inferElabV'45'RResolved'45'value'45'aux_1748 v0 v1 v2 v3 v5
du_inferElabV'45'RResolved'45'value'45'aux_1748 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RResolved'45'value'45'aux_1748 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_300 (coe v3)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v1 v5)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
             (coe
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v2
                v5)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                   (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))
                   (coe v3)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-lookup-aux
d_inferElabV'45'RVar'45'lookup'45'aux_1762 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'lookup'45'aux_1762 v0 v1 v2 ~v3 v4 ~v5
  = du_inferElabV'45'RVar'45'lookup'45'aux_1762 v0 v1 v2 v4
du_inferElabV'45'RVar'45'lookup'45'aux_1762 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'lookup'45'aux_1762 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_success_300 (coe v5) (coe v7)
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_526 (coe v8))
                              (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_60 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    du_inferElabV'45'RVar'45'import'45'value'45'aux_1774 (coe v0)
                    (coe v1) (coe v4)
                    (coe MAlonzo.Code.Once.CanonicalName.d_genWord'63'_48 (coe v1))
                    (coe MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63'_52 (coe v4))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    du_inferElabV'45'RVar'45'poly'45'aux_1266 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Classify.d_classifyBareBuiltin_1792
                       (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RVar-import-value-aux
d_inferElabV'45'RVar'45'import'45'value'45'aux_1774 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RVar'45'import'45'value'45'aux_1774 v0 v1 ~v2 v3
                                                    ~v4 v5 ~v6 v7 ~v8
  = du_inferElabV'45'RVar'45'import'45'value'45'aux_1774
      v0 v1 v3 v5 v7
du_inferElabV'45'RVar'45'import'45'value'45'aux_1774 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RVar'45'import'45'value'45'aux_1774 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe
                    seq (coe v6)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C_failure_302
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8 (coe v1)))
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             else coe
                    seq (coe v6)
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_300 (coe v2)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                                    (MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v1)) v7)
                                 (coe (0 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                    (coe v0)))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_86 v7)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_failure_302
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Error.C_NonConcreteSigOpType_20
                                    (coe v1) (coe v2)))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-other-aux
d_inferElabV'45'RApp'45'other'45'aux_1784 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_1092 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'other'45'aux_1784 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RApp'45'other'45'aux_1784 v0 v1 v2 v3
du_inferElabV'45'RApp'45'other'45'aux_1784 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_1092 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RApp'45'other'45'aux_1784 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe
                      ("unreachable: ahv-other \8658 classifyAppHead nothing"
                       ::
                       Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> let v4 = d_inferElabV_1460 (coe v0) (coe v1) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_300 v7 v8 v9 v10 v11
                         -> case coe v7 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                -> case coe v13 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Type.C_pure_34
                                              -> let v17
                                                       = coe
                                                           du_checkElabV'45'wf_1476 (coe v0)
                                                           (coe v2) (coe v12) in
                                                 coe
                                                   (case coe v17 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                        -> case coe v18 of
                                                             C_success_324 v20 v21 v22 v23
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       C_success_300 (coe v14)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                          (coe v8)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                             (coe v15) (coe v20)))
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_app_48
                                                                          v8 v20 v12 v15 v9 v21)
                                                                       (coe
                                                                          MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                          (coe v10) (coe v22))
                                                                       (coe v23))
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342
                                                                       v12 v15 v8 v20 v6 v19)
                                                             C_failure_326 v20
                                                               -> coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe C_failure_302 (coe v20))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            MAlonzo.Code.Once.Type.C_eff_36
                                              -> case coe v15 of
                                                   MAlonzo.Code.Once.Type.C_Zero_6
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_302
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                                                (coe v7)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   MAlonzo.Code.Once.Type.C_One_8
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             C_failure_302
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                                                (coe v7)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                     -> let v17
                                                              = coe
                                                                  du_checkElabV'45'wf_1476 (coe v0)
                                                                  (coe v2) (coe v12) in
                                                        coe
                                                          (case coe v17 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                               -> case coe v18 of
                                                                    C_success_324 v20 v21 v22 v23
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_success_300
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Type.C_Unit_118)
                                                                                 (coe v13)
                                                                                 (coe v14))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                 (coe v8) (coe v20))
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_effApp_62
                                                                                 v8 v20 v12 v9 v21)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                 (coe v10)
                                                                                 (coe v22))
                                                                              (coe v23))
                                                                           (coe
                                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358
                                                                              v12 v8 v20 v6 v19)
                                                                    C_failure_326 v20
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_failure_302
                                                                              (coe v20))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_NotFunction_64
                                           (coe v7)))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_302 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RApp-dispatch
d_inferElabV'45'RApp'45'dispatch_1794 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_1122 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RApp'45'dispatch_1794 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RApp'45'dispatch_1794 v0 v1 v2 v3
du_inferElabV'45'RApp'45'dispatch_1794 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_1122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RApp'45'dispatch_1794 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'id_1124
        -> let v4 = d_inferElabV_1460 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_300 (coe v7)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v8 v7
                                    (coe MAlonzo.Code.Once.IR.C_id_22) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278 v8 v6)
                       C_failure_302 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'fst_1126
        -> let v4 = d_inferElabV_1460 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_300 v7 v8 v9 v10 v11
                         -> case coe v7 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_300 (coe v12)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v8 v7
                                           (coe MAlonzo.Code.Once.IR.C_fst_44) v9)
                                        (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290
                                        v13 v8 v6)
                              MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_302 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'snd_1128
        -> let v4 = d_inferElabV_1460 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_300 v7 v8 v9 v10 v11
                         -> case coe v7 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_300 (coe v13)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v8 v7
                                           (coe MAlonzo.Code.Once.IR.C_snd_50) v9)
                                        (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302
                                        v12 v8 v6)
                              MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_302 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'terminal_1130
        -> let v4 = d_inferElabV_1460 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_300 (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v8 v7
                                    (coe MAlonzo.Code.Once.IR.C_terminal_74) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_312 v7
                                 v8 v6)
                       C_failure_302 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inl_1132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlInInferMode_28))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inr_1134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrInInferMode_30))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'initial_1136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe MAlonzo.Code.Once.TypeCheck.Error.C_InitialInInferMode_32))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'curry_1138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("curry" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'apply_1140
        -> let v4 = d_inferElabV_1460 (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C_success_300 v7 v8 v9 v10 v11
                         -> case coe v7 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                                -> case coe v12 of
                                     MAlonzo.Code.Once.Type.C_Unit_118
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_302
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_Void_120
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_302
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C__'42'__122 v14 v15
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_302
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C__'43'__124 v14 v15
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_302
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
                                       -> case coe v15 of
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                                              -> case coe v17 of
                                                   MAlonzo.Code.Once.Type.C_Zero_6
                                                     -> coe
                                                          seq (coe v18)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_302
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   MAlonzo.Code.Once.Type.C_One_8
                                                     -> coe
                                                          seq (coe v18)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                C_failure_302
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                   (coe
                                                                      ("apply" :: Data.Text.Text))))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                     -> case coe v18 of
                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                            -> let v19
                                                                     = d__'8799'T__224
                                                                         (coe v14) (coe v13) in
                                                               coe
                                                                 (case coe v19 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                      -> if coe v20
                                                                           then coe
                                                                                  seq (coe v21)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        C_success_300
                                                                                        (coe v16)
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                 (coe
                                                                                                    v0)))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                              (coe
                                                                                                 v17)
                                                                                              (coe
                                                                                                 v8)))
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426
                                                                                           v8
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.Type.C__'42'__122
                                                                                              (coe
                                                                                                 v12)
                                                                                              (coe
                                                                                                 v14))
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.IR.C_apply_92)
                                                                                           v9)
                                                                                        (coe
                                                                                           addInt
                                                                                           (coe
                                                                                              (1 ::
                                                                                                 Integer))
                                                                                           (coe
                                                                                              v10))
                                                                                        (coe v11))
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324
                                                                                        v14 v8 v6))
                                                                           else coe
                                                                                  seq (coe v21)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        C_failure_302
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                           (coe
                                                                                              ("apply"
                                                                                               ::
                                                                                               Data.Text.Text))))
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          MAlonzo.Code.Once.Type.C_eff_36
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    C_failure_302
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                       (coe
                                                                          ("apply"
                                                                           ::
                                                                           Data.Text.Text))))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Type.C_μ'45'type_128 v14
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_302
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_ν'45'type_130 v14
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_302
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_Int_132
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_302
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_Float_134
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_302
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_Str_136
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_302
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     MAlonzo.Code.Once.Type.C_Buffer_138
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_302
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                  (coe ("apply" :: Data.Text.Text))))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v12
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_failure_302
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                           (coe ("apply" :: Data.Text.Text))))
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_302 v7
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'In_1142
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("In" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'cata_1144
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("cata" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'pair'45'applied_1148
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("pair" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'compose'45'applied_1152
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("compose" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'case'45'applied_1156
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                   (coe ("case" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'other_1160
        -> coe
             d_inferElabV'45'RApp'45'other_1484 (coe v0) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RApp-dispatch
d_checkElabV'45'RApp'45'dispatch_1806 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_1122 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RApp'45'dispatch_1806 v0 v1 v2 v3 v4 ~v5
  = du_checkElabV'45'RApp'45'dispatch_1806 v0 v1 v2 v3 v4
du_checkElabV'45'RApp'45'dispatch_1806 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_1122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RApp'45'dispatch_1806 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'id_1124
        -> let v5 = d_inferElabV_1460 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_300 v8 v9 v10 v11 v12
                         -> let v13
                                  = coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_300 (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v9
                                            v8 (coe MAlonzo.Code.Once.IR.C_id_22) v10)
                                         (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278
                                         v9 v7) in
                            coe (coe du_embedOrSubsume_568 (coe v3) (coe v13))
                       C_failure_302 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'fst_1126
        -> let v5 = d_inferElabV_1460 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_300 v8 v9 v10 v11 v12
                         -> case coe v8 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                C_success_300 (coe v13)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                         (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426
                                                   v9 v8 (coe MAlonzo.Code.Once.IR.C_fst_44) v10)
                                                (coe addInt (coe (1 :: Integer)) (coe v11))
                                                (coe v12))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290
                                                v14 v9 v7) in
                                   coe (coe du_embedOrSubsume_568 (coe v3) (coe v15))
                              MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v15))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                -> let v16
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v16))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                                -> let v14
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v14))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v13
                                -> let v14
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v14))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_FstNeedsPair_38 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_302 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'snd_1128
        -> let v5 = d_inferElabV_1460 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_300 v8 v9 v10 v11 v12
                         -> case coe v8 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe
                                                C_success_300 (coe v14)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                         (coe v0)))
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v9)))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426
                                                   v9 v8 (coe MAlonzo.Code.Once.IR.C_snd_50) v10)
                                                (coe addInt (coe (1 :: Integer)) (coe v11))
                                                (coe v12))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302
                                                v13 v9 v7) in
                                   coe (coe du_embedOrSubsume_568 (coe v3) (coe v15))
                              MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v15))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                -> let v16
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v16))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                                -> let v14
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v14))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v13
                                -> let v14
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v14))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_SndNeedsPair_40 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_302 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'terminal_1130
        -> let v5 = d_inferElabV_1460 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_300 v8 v9 v10 v11 v12
                         -> let v13
                                  = coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         C_success_300 (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9)))
                                         (coe
                                            MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v9
                                            v8 (coe MAlonzo.Code.Once.IR.C_terminal_74) v10)
                                         (coe addInt (coe (1 :: Integer)) (coe v11)) (coe v12))
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_312
                                         v8 v9 v7) in
                            coe (coe du_embedOrSubsume_568 (coe v3) (coe v13))
                       C_failure_302 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inl_1132
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__122 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'43'__124 v5 v6
               -> let v7
                        = coe du_checkElabV'45'wf_1476 (coe v0) (coe v2) (coe v5) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v8 of
                              C_success_324 v10 v11 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_324
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v10
                                           v5
                                           (coe
                                              MAlonzo.Code.Once.IR.C_inl_56
                                              (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                           v11)
                                        (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_584
                                        v10 v9)
                              C_failure_326 v10
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InlNeedsSumType_34))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'inr_1134
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__122 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'43'__124 v5 v6
               -> let v7
                        = coe du_checkElabV'45'wf_1476 (coe v0) (coe v2) (coe v6) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v8 of
                              C_success_324 v10 v11 v12 v13
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        C_success_324
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v10
                                           v6
                                           (coe
                                              MAlonzo.Code.Once.IR.C_inr_62
                                              (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                           v11)
                                        (coe addInt (coe (1 :: Integer)) (coe v12)) (coe v13))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_596
                                        v10 v9)
                              C_failure_326 v10
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v5 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       C_failure_326
                       (coe MAlonzo.Code.Once.TypeCheck.Error.C_InrNeedsSumType_36))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'initial_1136
        -> let v5
                 = coe
                     du_checkElabV'45'wf_1476 (coe v0) (coe v2)
                     (coe MAlonzo.Code.Once.Type.C_Void_120) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_324 v8 v9 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_324
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v8
                                    (coe MAlonzo.Code.Once.Type.C_Void_120)
                                    (coe MAlonzo.Code.Once.IR.C_initial_78) v9)
                                 (coe addInt (coe (1 :: Integer)) (coe v10)) (coe v11))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_606
                                 v8 v7)
                       C_failure_326 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'curry_1138
        -> coe d_checkCurry_1398 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'apply_1140
        -> let v5 = d_inferElabV_1460 (coe v0) (coe v2) in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v6 of
                       C_success_300 v8 v9 v10 v11 v12
                         -> case coe v8 of
                              MAlonzo.Code.Once.Type.C_Unit_118
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Void_120
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                                -> case coe v13 of
                                     MAlonzo.Code.Once.Type.C_Unit_118
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_326 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_Void_120
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_326 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C__'42'__122 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_326 (coe v17))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C__'43'__124 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_326 (coe v17))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                              -> case coe v18 of
                                                   MAlonzo.Code.Once.Type.C_Zero_6
                                                     -> let v20
                                                              = seq
                                                                  (coe v19)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        C_failure_302
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                           (coe
                                                                              ("apply"
                                                                               ::
                                                                               Data.Text.Text))))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                        coe
                                                          (case coe v20 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                               -> case coe v21 of
                                                                    C_success_300 v23 v24 v25 v26 v27
                                                                      -> coe
                                                                           du_embedOrSubsume_568
                                                                           (coe v3) (coe v20)
                                                                    C_failure_302 v23
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_failure_326
                                                                              (coe v23))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   MAlonzo.Code.Once.Type.C_One_8
                                                     -> let v20
                                                              = seq
                                                                  (coe v19)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        C_failure_302
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                           (coe
                                                                              ("apply"
                                                                               ::
                                                                               Data.Text.Text))))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                        coe
                                                          (case coe v20 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                               -> case coe v21 of
                                                                    C_success_300 v23 v24 v25 v26 v27
                                                                      -> coe
                                                                           du_embedOrSubsume_568
                                                                           (coe v3) (coe v20)
                                                                    C_failure_302 v23
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              C_failure_326
                                                                              (coe v23))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                   MAlonzo.Code.Once.Type.C_Many_10
                                                     -> case coe v19 of
                                                          MAlonzo.Code.Once.Type.C_pure_34
                                                            -> let v20
                                                                     = d__'8799'T__224
                                                                         (coe v15) (coe v14) in
                                                               coe
                                                                 (case coe v20 of
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                      -> if coe v21
                                                                           then let v23
                                                                                      = seq
                                                                                          (coe v22)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                C_success_300
                                                                                                (coe
                                                                                                   v17)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                                                         (coe
                                                                                                            v0)))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                                                      (coe
                                                                                                         v18)
                                                                                                      (coe
                                                                                                         v9)))
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426
                                                                                                   v9
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.Type.C__'42'__122
                                                                                                      (coe
                                                                                                         v13)
                                                                                                      (coe
                                                                                                         v15))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Once.IR.C_apply_92)
                                                                                                   v10)
                                                                                                (coe
                                                                                                   addInt
                                                                                                   (coe
                                                                                                      (1 ::
                                                                                                         Integer))
                                                                                                   (coe
                                                                                                      v11))
                                                                                                (coe
                                                                                                   v12))
                                                                                             (coe
                                                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324
                                                                                                v15
                                                                                                v9
                                                                                                v7)) in
                                                                                coe
                                                                                  (case coe v23 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                       -> case coe
                                                                                                 v24 of
                                                                                            C_success_300 v26 v27 v28 v29 v30
                                                                                              -> coe
                                                                                                   du_embedOrSubsume_568
                                                                                                   (coe
                                                                                                      v3)
                                                                                                   (coe
                                                                                                      v23)
                                                                                            C_failure_302 v26
                                                                                              -> coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                   (coe
                                                                                                      C_failure_326
                                                                                                      (coe
                                                                                                         v26))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           else (let v23
                                                                                       = seq
                                                                                           (coe v22)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 C_failure_302
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                                                    (coe
                                                                                                       ("apply"
                                                                                                        ::
                                                                                                        Data.Text.Text))))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) in
                                                                                 coe
                                                                                   (case coe v23 of
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                                        -> case coe
                                                                                                  v24 of
                                                                                             C_success_300 v26 v27 v28 v29 v30
                                                                                               -> coe
                                                                                                    du_embedOrSubsume_568
                                                                                                    (coe
                                                                                                       v3)
                                                                                                    (coe
                                                                                                       v23)
                                                                                             C_failure_302 v26
                                                                                               -> coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    (coe
                                                                                                       C_failure_326
                                                                                                       (coe
                                                                                                          v26))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                          MAlonzo.Code.Once.Type.C_eff_36
                                                            -> let v20
                                                                     = coe
                                                                         MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                                         (coe
                                                                            ("apply"
                                                                             ::
                                                                             Data.Text.Text)) in
                                                               coe
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe C_failure_326 (coe v20))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Type.C_μ'45'type_128 v15
                                       -> let v16
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_326 (coe v16))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_ν'45'type_130 v15
                                       -> let v16
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_326 (coe v16))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_Int_132
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_326 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_Float_134
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_326 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_Str_136
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_326 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     MAlonzo.Code.Once.Type.C_Buffer_138
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                    (coe ("apply" :: Data.Text.Text)) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe C_failure_326 (coe v15))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v15))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                -> let v16
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v16))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                                -> let v14
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v14))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_ν'45'type_130 v13
                                -> let v14
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v14))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Int_132
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Float_134
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Str_136
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              MAlonzo.Code.Once.Type.C_Buffer_138
                                -> let v13
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                             (coe ("apply" :: Data.Text.Text)) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe C_failure_326 (coe v13))
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       C_failure_302 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v8))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'In_1142
        -> coe d_checkIn_1414 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'cata_1144
        -> coe d_checkCata_1432 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'pair'45'applied_1148
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
               -> coe
                    d_checkPair_1326 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                          (coe
                             MAlonzo.Code.Once.CanonicalName.C_canonical_10
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe ("Generators" :: Data.Text.Text))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe ("pair" :: Data.Text.Text))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v7))
                    (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'compose'45'applied_1152
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
               -> coe
                    d_checkCompose_1374 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                          (coe
                             MAlonzo.Code.Once.CanonicalName.C_canonical_10
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe ("Generators" :: Data.Text.Text))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe ("compose" :: Data.Text.Text))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v7))
                    (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'case'45'applied_1156
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
               -> coe
                    d_checkCase_1348 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40
                          (coe
                             MAlonzo.Code.Once.CanonicalName.C_canonical_10
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe ("Generators" :: Data.Text.Text))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe ("case" :: Data.Text.Text))
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
                       (coe v7))
                    (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Classify.C_ahv'45'other_1160
        -> let v6
                 = coe
                     du_inferElabV'45'RApp'45'dispatch_1794 (coe v0) (coe v1) (coe v2)
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHeadView_1164
                        (coe v1)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_300 v9 v10 v11 v12 v13
                         -> coe du_embedOrSubsume_568 (coe v3) (coe v6)
                       C_failure_302 v9
                         -> coe
                              du_checkElabV'45'RApp'45'other'45'argdriven'45'aux_1820 (coe v0)
                              (coe v1) (coe v2) (coe v3) (coe v9)
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_classifyAppHead_1370
                                 (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RApp-other-argdriven-aux
d_checkElabV'45'RApp'45'other'45'argdriven'45'aux_1820 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_1092 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RApp'45'other'45'argdriven'45'aux_1820 v0 v1 v2 v3
                                                       v4 v5 ~v6
  = du_checkElabV'45'RApp'45'other'45'argdriven'45'aux_1820
      v0 v1 v2 v3 v4 v5
du_checkElabV'45'RApp'45'other'45'argdriven'45'aux_1820 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_1092 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RApp'45'other'45'argdriven'45'aux_1820 v0 v1 v2 v3
                                                        v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v4))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> let v6 = d_inferElabV_1460 (coe v0) (coe v2) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_300 v9 v10 v11 v12 v13
                         -> let v14 = d_classifyEffArrow_458 (coe v3) in
                            coe
                              (case coe v14 of
                                 C_eav'45'eff_450
                                   -> case coe v3 of
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                                          -> let v20
                                                   = coe
                                                       du_checkElabV'45'wf_1476 (coe v0) (coe v1)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                          (coe v9)
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                             (coe v17)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_pure_34))
                                                             (coe v19))) in
                                             coe
                                               (case coe v20 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                    -> case coe v21 of
                                                         C_success_324 v23 v24 v25 v26
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   C_success_324
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                                      (coe v23)
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C_Many_10)
                                                                         (coe v10)))
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Syntax.C_app_48
                                                                         v23 v10 v9
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C_Many_10)
                                                                         v24 v11))
                                                                   (coe
                                                                      addInt (coe (1 :: Integer))
                                                                      (coe
                                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                         (coe v25) (coe v12)))
                                                                   (coe v26))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_634
                                                                      v9 v23 v10 v8 v22))
                                                         C_failure_326 v23
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v21)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_eav'45'other_454
                                   -> let v16
                                            = coe
                                                du_checkElabV'45'wf_1476 (coe v0) (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                   (coe v9)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                   (coe v3)) in
                                      coe
                                        (case coe v16 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                             -> case coe v17 of
                                                  C_success_324 v19 v20 v21 v22
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            C_success_324
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                               (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                  (coe v10)))
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Syntax.C_app_48
                                                               v19 v10 v9
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                               v20 v11)
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v21) (coe v12)))
                                                            (coe v22))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_634
                                                            v9 v19 v10 v8 v18)
                                                  C_failure_326 v19
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe v17)
                                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_failure_302 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v9))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-failure-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_1828 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_1828 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_326 (coe v2))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe C_failure_326 (coe v2))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> let v8 = d__'8799'T__224 (coe v3) (coe v5) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                -> if coe v9
                                     then coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_success_324
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                        (coe v0)))
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                     (coe MAlonzo.Code.Once.IR.C_id_22))
                                                  (coe (0 :: Integer))
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_366))
                                     else coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  C_failure_326
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                     (coe ("id" :: Data.Text.Text))))
                                               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-failure-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_1836 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_1836 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> case coe v4 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v8 v9
                      -> case coe v8 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_One_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> let v10 = d__'8799'T__224 (coe v6) (coe v5) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_success_324
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                            (coe MAlonzo.Code.Once.IR.C_fst_44))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_376))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_326
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                            (coe ("fst" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-failure-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_1844 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_1844 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_120
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> case coe v4 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v8 v9
                      -> case coe v8 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_One_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> let v10 = d__'8799'T__224 (coe v7) (coe v5) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_success_324
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                            (coe MAlonzo.Code.Once.IR.C_snd_50))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_386))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_326
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                            (coe ("snd" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-failure-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_1852 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_1852 v0
                                                               v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> case coe v5 of
                           MAlonzo.Code.Once.Type.C_Unit_118
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_324
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                           (coe v0)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                        (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                        (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_394)
                           MAlonzo.Code.Once.Type.C_Void_120
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'42'__122 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Int_132
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Float_134
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Str_136
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Buffer_138
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-failure-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_1860 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_1860 v0 v1
                                                              v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_Unit_118
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Void_120
               -> case coe v4 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
                      -> case coe v6 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_One_8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     C_success_324
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                           (coe v0)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                        (coe MAlonzo.Code.Once.IR.C_initial_78))
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                        (coe v0)))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_402)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'43'__124 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_μ'45'type_128 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_ν'45'type_130 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Int_132
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Float_134
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Str_136
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             MAlonzo.Code.Once.Type.C_Buffer_138
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C_failure_326 (coe v2))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_1868 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_1868 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> case coe v5 of
                           MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
                             -> let v10 = d__'8799'T__224 (coe v3) (coe v8) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_success_324
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                            (coe
                                                               MAlonzo.Code.Once.IR.C_inl_56
                                                               (coe MAlonzo.Code.Once.IR.C_Heap_8)))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_412))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_326
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                            (coe ("inl" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Type.C_Unit_118
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Void_120
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'42'__122 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Int_132
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Float_134
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Str_136
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Buffer_138
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-failure-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_1876 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Error.T_TypeError_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_1876 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           seq (coe v5)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v2))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> case coe v5 of
                           MAlonzo.Code.Once.Type.C__'43'__124 v8 v9
                             -> let v10 = d__'8799'T__224 (coe v3) (coe v9) in
                                coe
                                  (case coe v10 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                       -> if coe v11
                                            then coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_success_324
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                               (coe v0)))
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                            (coe
                                                               MAlonzo.Code.Once.IR.C_inr_62
                                                               (coe MAlonzo.Code.Once.IR.C_Heap_8)))
                                                         (coe (0 :: Integer))
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                            (coe v0)))
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_422))
                                            else coe
                                                   seq (coe v12)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         C_failure_326
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Error.C_BuiltinTypeMismatch_76
                                                            (coe ("inr" :: Data.Text.Text))))
                                                      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.Type.C_Unit_118
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Void_120
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'42'__122 v8 v9
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v8 v9 v10
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v8
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Int_132
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Float_134
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Str_136
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           MAlonzo.Code.Once.Type.C_Buffer_138
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe C_failure_326 (coe v2))
                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe C_failure_326 (coe v2))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-id-aux
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_1882 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'id'45'aux_1882 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_300 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_568 (coe v1) (coe v2)
             C_failure_302 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'id'45'failure'45'aux_1828 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-fst-aux
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_1888 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_1888 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_300 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_568 (coe v1) (coe v2)
             C_failure_302 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'fst'45'failure'45'aux_1836 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-snd-aux
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_1894 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_1894 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_300 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_568 (coe v1) (coe v2)
             C_failure_302 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'snd'45'failure'45'aux_1844 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-terminal-aux
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_1900 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_1900 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_300 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_568 (coe v1) (coe v2)
             C_failure_302 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'terminal'45'failure'45'aux_1852
                    (coe v0) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-initial-aux
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_1906 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_1906 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_300 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_568 (coe v1) (coe v2)
             C_failure_302 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'initial'45'failure'45'aux_1860
                    (coe v0) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inl-aux
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_1912 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_1912 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_300 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_568 (coe v1) (coe v2)
             C_failure_302 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'inl'45'failure'45'aux_1868 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-inr-aux
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_1918 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_1918 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_success_300 v5 v6 v7 v8 v9
               -> coe du_embedOrSubsume_568 (coe v1) (coe v2)
             C_failure_302 v5
               -> coe
                    d_checkElabV'45'RVar'45'bbc'45'inr'45'failure'45'aux_1876 (coe v0)
                    (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.inferElabV-RResolved-dispatch
d_inferElabV'45'RResolved'45'dispatch_1924 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_1458 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RResolved'45'dispatch_1924 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_1460
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("id" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_1462
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("fst" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_1464
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("snd" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_1466
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("terminal" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_1468
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("initial" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_1470
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inl" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_1472
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_failure_302
                (coe
                   MAlonzo.Code.Once.TypeCheck.Error.C_UnboundVariable_8
                   (coe ("inr" :: Data.Text.Text))))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_1474
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                C_success_300 (coe MAlonzo.Code.Once.Type.C_Unit_118)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_48)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_1478 v4
        -> coe
             du_inferElabV'45'RResolved'45'aux_1692 (coe v0) (coe v1) (coe v4)
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RResolved-dispatch
d_checkElabV'45'RResolved'45'dispatch_1932 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_1458 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RResolved'45'dispatch_1932 v0 ~v1 v2 v3 v4
  = du_checkElabV'45'RResolved'45'dispatch_1932 v0 v2 v3 v4
du_checkElabV'45'RResolved'45'dispatch_1932 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_GenView_1458 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RResolved'45'dispatch_1932 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'id_1460
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'id'45'aux_1882 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'fst_1462
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'fst'45'aux_1888 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'snd_1464
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'snd'45'aux_1894 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'terminal_1466
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'terminal'45'aux_1900 (coe v0)
             (coe v1) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'initial_1468
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'initial'45'aux_1906 (coe v0)
             (coe v1) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inl_1470
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inl'45'aux_1912 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'inr_1472
        -> coe
             d_checkElabV'45'RVar'45'bbc'45'inr'45'aux_1918 (coe v0) (coe v1)
             (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'unit_1474
        -> coe du_embedOrSubsume_568 (coe v1) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Classify.C_gv'45'other_1478 v5
        -> coe du_embedOrSubsume_568 (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RVar-bbc-other-aux
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_1940 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RVar'45'bbc'45'other'45'aux_1940 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             C_success_300 v6 v7 v8 v9 v10
               -> coe du_embedOrSubsume_568 (coe v2) (coe v3)
             C_failure_302 v6
               -> let v7
                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPoly_48
                            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364 (coe v0))
                            (coe v1) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 C_success_324
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v1)
                                 (coe (0 :: Integer))
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                    (coe v0)))
                              (coe d_bbc'45'other'45'poly'45'witness_1206 v0 v1 v2)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v6))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.checkElabV-RInt-aux
d_checkElabV'45'RInt'45'aux_1948 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RInt'45'aux_1948 v0 v1 v2
  = let v3
          = coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_22 in
    coe
      (let v4 = coe MAlonzo.Code.Once.Type.C_Int_132 in
       coe
         (let v5
                = MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                    (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)) in
          coe
            (let v6 = coe MAlonzo.Code.Once.Surface.Syntax.C_int_184 v1 in
             coe
               (let v7 = 0 :: Integer in
                coe
                  (let v8
                         = MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                             (coe v0) in
                   coe
                     (let v9 = d__'8799'T__224 (coe v2) (coe v4) in
                      coe
                        (case coe v9 of
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                             -> if coe v10
                                  then coe
                                         seq (coe v11)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe C_success_324 (coe v5) (coe v6) (coe v7) (coe v8))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516
                                               v3))
                                  else coe
                                         seq (coe v11)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               C_failure_326
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                  (coe v2) (coe v4)))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                           _ -> MAlonzo.RTE.mazUnreachableError)))))))
-- Once.TypeCheck.Elaborate.checkElabV-RFloat-aux
d_checkElabV'45'RFloat'45'aux_1962 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RFloat'45'aux_1962 v0 v1 v2 v3 ~v4 v5
  = du_checkElabV'45'RFloat'45'aux_1962 v0 v1 v2 v3 v5
du_checkElabV'45'RFloat'45'aux_1962 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElabV'45'RFloat'45'aux_1962 v0 v1 v2 v3 v4
  = let v5
          = d__'8799'T__224
              (coe v4) (coe MAlonzo.Code.Once.Type.C_Float_134) in
    coe
      (case coe v5 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
           -> if coe v6
                then coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_success_324
                             (coe
                                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                             (coe
                                MAlonzo.Code.Once.Surface.Syntax.C_float_198
                                (MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
                                   (coe v1) (coe v2) (coe v3)))
                             (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516
                             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_34)))
                else coe
                       seq (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_failure_326
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60 (coe v4)
                                (coe MAlonzo.Code.Once.Type.C_Float_134)))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Elaborate.inferElabV-RFloat-aux
d_inferElabV'45'RFloat'45'aux_1974 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inferElabV'45'RFloat'45'aux_1974 v0 v1 v2 v3 ~v4
  = du_inferElabV'45'RFloat'45'aux_1974 v0 v1 v2 v3
du_inferElabV'45'RFloat'45'aux_1974 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inferElabV'45'RFloat'45'aux_1974 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         C_success_300 (coe MAlonzo.Code.Once.Type.C_Float_134)
         (coe
            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
            (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
         (coe
            MAlonzo.Code.Once.Surface.Syntax.C_float_198
            (MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
               (coe v1) (coe v2) (coe v3)))
         (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0)))
      (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_34)
-- Once.TypeCheck.Elaborate.checkElabV-RPair-aux
d_checkElabV'45'RPair'45'aux_1984 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  T_RPairTarget_174 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElabV'45'RPair'45'aux_1984 v0 v1 v2 v3 v4
  = case coe v4 of
      C_rpt'45'prod_180
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
               -> coe
                    d_checkPairLit_1338 (coe v0) (coe v1) (coe v2) (coe v7) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rpt'45'vlift_190
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
               -> case coe v10 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v12 v13
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              C_failure_326
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v13))
                                    (coe v11))
                                 (coe v11)))
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rpt'45'other_194
        -> let v6
                 = coe
                     du_inferElabV'45'RPair'45'aux_1492
                     (coe d_inferElabV_1460 (coe v0) (coe v1))
                     (coe d_inferElabV_1460 (coe v0) (coe v2)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v7 of
                       C_success_300 v9 v10 v11 v12 v13
                         -> let v14 = d__'8799'T__224 (coe v3) (coe v9) in
                            coe
                              (case coe v14 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                   -> if coe v15
                                        then coe
                                               seq (coe v16)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     C_success_324 (coe v10) (coe v11) (coe v12)
                                                     (coe v13))
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516
                                                     v8))
                                        else coe
                                               seq (coe v16)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     C_failure_326
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Error.C_TypeMismatch_60
                                                        (coe v3) (coe v9)))
                                                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_failure_302 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C_failure_326 (coe v9))
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.ext-arrow-info
d_ext'45'arrow'45'info_1994 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_ext'45'arrow'45'info_1994 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v5 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe
             MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182
             (coe
                MAlonzo.Code.Once.CanonicalName.d_bare_12
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("." :: Data.Text.Text) v4)))
             (coe
                MAlonzo.Code.Once.SigOp.Info.C_pureV_140
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'semM_416 v0 v1
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v4))))
             (coe v6)
             (coe MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152 (coe v7))
      MAlonzo.Code.Once.Type.C_eff_36
        -> let v8
                 = d__'8799'T__224
                     (coe v1) (coe MAlonzo.Code.Once.Type.C_Unit_118) in
           coe
             (case coe v8 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                  -> if coe v9
                       then coe
                              seq (coe v10)
                              (let v11
                                     = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupSigEffect_14
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_366
                                            (coe v2))
                                         (coe
                                            MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                                            (coe
                                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                               ("." :: Data.Text.Text) v4)) in
                               coe
                                 (case coe v11 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                      -> case coe v12 of
                                           MAlonzo.Code.Once.SigEffect.C_emits_6
                                             -> coe
                                                  MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182
                                                  (coe
                                                     MAlonzo.Code.Once.CanonicalName.d_bare_12
                                                     (coe
                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                        v3
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           ("." :: Data.Text.Text) v4)))
                                                  (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_142)
                                                  (coe v6)
                                                  (coe
                                                     MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152
                                                     (coe v7))
                                           MAlonzo.Code.Once.SigEffect.C_halts_8
                                             -> coe
                                                  MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182
                                                  (coe
                                                     MAlonzo.Code.Once.CanonicalName.d_bare_12
                                                     (coe
                                                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                        v3
                                                        (coe
                                                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                           ("." :: Data.Text.Text) v4)))
                                                  (coe MAlonzo.Code.Once.SigOp.Info.C_haltsV_144)
                                                  (coe v6)
                                                  (coe
                                                     MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152
                                                     (coe v7))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe
                                           MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182
                                           (coe
                                              MAlonzo.Code.Once.CanonicalName.d_bare_12
                                              (coe
                                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                                                 (coe
                                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                                    ("." :: Data.Text.Text) v4)))
                                           (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_142) (coe v6)
                                           (coe
                                              MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152
                                              (coe v7))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       else coe
                              seq (coe v10)
                              (coe
                                 MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182
                                 (coe
                                    MAlonzo.Code.Once.CanonicalName.d_bare_12
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("." :: Data.Text.Text) v4)))
                                 (coe
                                    MAlonzo.Code.Once.SigOp.Info.C_pureV_140
                                    (coe
                                       MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'semM_416
                                       v0 v1
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v3
                                          (coe
                                             MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                             ("." :: Data.Text.Text) v4))))
                                 (coe v6)
                                 (coe MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152 (coe v7)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.ext-resolved-info-aux
d_ext'45'resolved'45'info'45'aux_2000 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Once.SigEffect.T_SigEffect_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_ext'45'resolved'45'info'45'aux_2000 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v3 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe
             MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182 (coe v2)
             (coe
                MAlonzo.Code.Once.SigOp.Info.C_pureV_140
                (coe
                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'semM_416 v0 v1
                   (MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v2))))
             (coe v6)
             (coe MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152 (coe v7))
      MAlonzo.Code.Once.Type.C_eff_36
        -> case coe v4 of
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
               -> if coe v8
                    then coe
                           seq (coe v9)
                           (case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                -> case coe v10 of
                                     MAlonzo.Code.Once.SigEffect.C_emits_6
                                       -> coe
                                            MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182 (coe v2)
                                            (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_142) (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152
                                               (coe v7))
                                     MAlonzo.Code.Once.SigEffect.C_halts_8
                                       -> coe
                                            MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182 (coe v2)
                                            (coe MAlonzo.Code.Once.SigOp.Info.C_haltsV_144) (coe v6)
                                            (coe
                                               MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152
                                               (coe v7))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> coe
                                     MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182 (coe v2)
                                     (coe MAlonzo.Code.Once.SigOp.Info.C_emitsV_142) (coe v6)
                                     (coe
                                        MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152 (coe v7))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    else coe
                           seq (coe v9)
                           (coe
                              MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_182 (coe v2)
                              (coe
                                 MAlonzo.Code.Once.SigOp.Info.C_pureV_140
                                 (coe
                                    MAlonzo.Code.Once.Arith.SigOp.Builders.d_generic'45'semM_416 v0
                                    v1
                                    (MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v2))))
                              (coe v6)
                              (coe MAlonzo.Code.Once.SigOp.Info.C_ffi'45'concrete_152 (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Elaborate.ext-resolved-info
d_ext'45'resolved'45'info_2006 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160
d_ext'45'resolved'45'info_2006 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_ext'45'resolved'45'info'45'aux_2000 (coe v0) (coe v1) (coe v3)
      (coe v4) (coe MAlonzo.Code.Once.Type.d_isUnit'63'_160 (coe v1))
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_lookupSigEffect_14
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_366 (coe v2))
         (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v3)))
      (coe v5) (coe v6)
