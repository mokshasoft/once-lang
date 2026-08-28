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

module MAlonzo.Code.Once.TypeCheck.Morph where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Morph._≡T?_
d__'8801'T'63'__10 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d__'8801'T'63'__10 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Type.C_Unit_118
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Unit_118
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Void_120
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Void_120
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
                _ -> coe v2
         MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__122 v5 v6
                  -> let v7 = d__'8801'T'63'__10 (coe v3) (coe v5) in
                     coe
                       (let v8 = d__'8801'T'63'__10 (coe v4) (coe v6) in
                        coe
                          (case coe v7 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                _ -> coe v2
         MAlonzo.Code.Once.Type.C__'43'__124 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'43'__124 v5 v6
                  -> let v7 = d__'8801'T'63'__10 (coe v3) (coe v5) in
                     coe
                       (let v8 = d__'8801'T'63'__10 (coe v4) (coe v6) in
                        coe
                          (case coe v7 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                               -> case coe v8 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                      -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Int_132
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Int_132
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Float_134
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Float_134
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Str_136
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Str_136
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
                _ -> coe v2
         MAlonzo.Code.Once.Type.C_Buffer_138
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_Buffer_138
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 erased
                _ -> coe v2
         _ -> coe v2)
-- Once.TypeCheck.Morph.MorphRaw
d_MorphRaw_68 a0 = ()
data T_MorphRaw_68
  = C_mr'45'id_70 | C_mr'45'fst_72 | C_mr'45'snd_74 |
    C_mr'45'inl_76 | C_mr'45'inr_78 | C_mr'45'terminal_80 |
    C_mr'45'initial_82 | C_mr'45'case_88 T_MorphRaw_68 T_MorphRaw_68
-- Once.TypeCheck.Morph.morphRaw?
d_morphRaw'63'_92 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> Maybe T_MorphRaw_68
d_morphRaw'63'_92 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
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
                           (coe ("id" :: Data.Text.Text))) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                     -> if coe v4
                          then coe
                                 seq (coe v5)
                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_mr'45'id_70))
                          else coe
                                 seq (coe v5)
                                 (let v6
                                        = coe
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                            erased
                                            (\ v6 ->
                                               coe
                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                 (coe v2))
                                            (coe
                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                               (coe v2) (coe ("fst" :: Data.Text.Text))) in
                                  coe
                                    (case coe v6 of
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                         -> if coe v7
                                              then coe
                                                     seq (coe v8)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                        (coe C_mr'45'fst_72))
                                              else coe
                                                     seq (coe v8)
                                                     (let v9
                                                            = coe
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                erased
                                                                (\ v9 ->
                                                                   coe
                                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                     (coe v2))
                                                                (coe
                                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                   (coe v2)
                                                                   (coe
                                                                      ("snd" :: Data.Text.Text))) in
                                                      coe
                                                        (case coe v9 of
                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                             -> if coe v10
                                                                  then coe
                                                                         seq (coe v11)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                            (coe C_mr'45'snd_74))
                                                                  else coe
                                                                         seq (coe v11)
                                                                         (let v12
                                                                                = coe
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                    erased
                                                                                    (\ v12 ->
                                                                                       coe
                                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                         (coe v2))
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                       (coe v2)
                                                                                       (coe
                                                                                          ("inl"
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
                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                (coe
                                                                                                   C_mr'45'inl_76))
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
                                                                                                                v2))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                           (coe
                                                                                                              v2)
                                                                                                           (coe
                                                                                                              ("inr"
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
                                                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                    (coe
                                                                                                                       C_mr'45'inr_78))
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
                                                                                                                                    v2))
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                               (coe
                                                                                                                                  v2)
                                                                                                                               (coe
                                                                                                                                  ("terminal"
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
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                        (coe
                                                                                                                                           C_mr'45'terminal_80))
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
                                                                                                                                                        v2))
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                   (coe
                                                                                                                                                      v2)
                                                                                                                                                   (coe
                                                                                                                                                      ("initial"
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
                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                            (coe
                                                                                                                                                               C_mr'45'initial_82))
                                                                                                                                                  else coe
                                                                                                                                                         seq
                                                                                                                                                         (coe
                                                                                                                                                            v23)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                       _ -> MAlonzo.RTE.mazUnreachableError))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v6
                         -> let v7
                                  = coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v7 ->
                                         coe
                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                           (coe v6))
                                      (coe
                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                         (coe v6) (coe ("case" :: Data.Text.Text))) in
                            coe
                              (case coe v7 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                   -> if coe v8
                                        then case coe v9 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                                 -> let v11 = d_morphRaw'63'_92 (coe v5) in
                                                    coe
                                                      (let v12 = d_morphRaw'63'_92 (coe v3) in
                                                       coe
                                                         (case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                              -> case coe v12 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                          (coe
                                                                             C_mr'45'case_88 v13
                                                                             v14)
                                                                   _ -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                            _ -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        else coe
                                               seq (coe v9)
                                               (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.Morph.morphToIR
d_morphToIR_200 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_MorphRaw_68 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.IR.T_IR_16
d_morphToIR_200 v0 v1 v2 v3
  = case coe v1 of
      C_mr'45'id_70
        -> let v4 = d__'8801'T'63'__10 (coe v2) (coe v3) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.IR.C_id_22)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError)
      C_mr'45'fst_72
        -> let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C__'42'__122 v5 v6
                  -> let v7 = d__'8801'T'63'__10 (coe v5) (coe v3) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.IR.C_fst_44)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v4)
      C_mr'45'snd_74
        -> let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C__'42'__122 v5 v6
                  -> let v7 = d__'8801'T'63'__10 (coe v6) (coe v3) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe MAlonzo.Code.Once.IR.C_snd_50)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v4)
      C_mr'45'inl_76
        -> let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Type.C__'43'__124 v5 v6
                  -> let v7 = d__'8801'T'63'__10 (coe v2) (coe v5) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Once.IR.C_inl_56
                                    (coe MAlonzo.Code.Once.IR.C_Heap_8))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v4)
      C_mr'45'inr_78
        -> let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Type.C__'43'__124 v5 v6
                  -> let v7 = d__'8801'T'63'__10 (coe v2) (coe v6) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Once.IR.C_inr_62
                                    (coe MAlonzo.Code.Once.IR.C_Heap_8))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v7
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v4)
      C_mr'45'terminal_80
        -> let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Type.C_Unit_118
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.IR.C_terminal_74)
                _ -> coe v4)
      C_mr'45'initial_82
        -> let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C_Void_120
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.IR.C_initial_78)
                _ -> coe v4)
      C_mr'45'case_88 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
                      -> let v12 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
                         coe
                           (case coe v2 of
                              MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                                -> let v15
                                         = d_morphToIR_200 (coe v11) (coe v6) (coe v13) (coe v3) in
                                   coe
                                     (let v16
                                            = d_morphToIR_200
                                                (coe v9) (coe v7) (coe v14) (coe v3) in
                                      coe
                                        (case coe v15 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                             -> case coe v16 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Once.IR.C_case_70 v17 v18)
                                                  _ -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                           _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                              _ -> coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
