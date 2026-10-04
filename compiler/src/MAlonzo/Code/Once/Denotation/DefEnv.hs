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

module MAlonzo.Code.Once.Denotation.DefEnv where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Denotation.DefEnv.DefEnvOf
d_DefEnvOf_6 ::
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_DefEnvOf_6 = erased
-- Once.Denotation.DefEnv.defAt-found
d_defAt'45'found_30 ::
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_defAt'45'found_30 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_defAt'45'found_30 v8
du_defAt'45'found_30 :: AgdaAny -> AgdaAny
du_defAt'45'found_30 v0 = coe v0
-- Once.Denotation.DefEnv.tailAt-found
d_tailAt'45'found_48 ::
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_tailAt'45'found_48 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_tailAt'45'found_48 v8
du_tailAt'45'found_48 :: AgdaAny -> AgdaAny
du_tailAt'45'found_48 v0 = coe v0
-- Once.Denotation.DefEnv.defAt
d_defAt_64 ::
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_defAt_64 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_defAt_64 v1 v2 v6
du_defAt_64 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
du_defAt_64 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v6)
                    (case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> let v9
                                  = coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v9 ->
                                         coe
                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                           (coe v5))
                                      (coe
                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                         (coe v5) (coe v1)) in
                            coe
                              (case coe v9 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                   -> if coe v10
                                        then coe seq (coe v11) (coe v7)
                                        else coe
                                               seq (coe v11)
                                               (coe du_defAt_64 (coe v4) (coe v1) (coe v8))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DefEnv.tailAt
d_tailAt_132 ::
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_tailAt_132 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 ~v7 = du_tailAt_132 v1 v2 v6
du_tailAt_132 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
du_tailAt_132 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v6)
                    (case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> let v9
                                  = coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v9 ->
                                         coe
                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                           (coe v5))
                                      (coe
                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                         (coe v5) (coe v1)) in
                            coe
                              (case coe v9 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                   -> if coe v10
                                        then coe seq (coe v11) (coe v8)
                                        else coe
                                               seq (coe v11)
                                               (coe du_tailAt_132 (coe v4) (coe v1) (coe v8))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DefEnv.DefEnvAll
d_DefEnvAll_198 ::
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 ->
   AgdaAny -> AgdaAny -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> AgdaAny -> ()
d_DefEnvAll_198 = erased
-- Once.Denotation.DefEnv.defAt-all
d_defAt'45'all_240 ::
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 ->
   AgdaAny -> AgdaAny -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_defAt'45'all_240 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11
  = du_defAt'45'all_240 v3 v4 v8 v9 v10
du_defAt'45'all_240 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_defAt'45'all_240 v0 v1 v2 v3 v4
  = case coe v0 of
      (:) v5 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    seq (coe v8)
                    (case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> case coe v3 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> case coe v4 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                    erased
                                                    (\ v15 ->
                                                       coe
                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                         (coe v7))
                                                    (coe
                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                       (coe v7) (coe v1)) in
                                          coe
                                            (case coe v15 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                 -> if coe v16
                                                      then coe seq (coe v17) (coe v13)
                                                      else coe
                                                             seq (coe v17)
                                                             (coe
                                                                du_defAt'45'all_240 (coe v6)
                                                                (coe v1) (coe v10) (coe v12)
                                                                (coe v14))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DefEnv._.found
d_found_318 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 ->
   AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_found_318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19
  = du_found_318 v16
du_found_318 :: AgdaAny -> AgdaAny
du_found_318 v0 = coe v0
-- Once.Denotation.DefEnv.tailAt-all
d_tailAt'45'all_376 ::
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 ->
   AgdaAny -> AgdaAny -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_tailAt'45'all_376 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 ~v11
  = du_tailAt'45'all_376 v3 v4 v8 v9 v10
du_tailAt'45'all_376 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_tailAt'45'all_376 v0 v1 v2 v3 v4
  = case coe v0 of
      (:) v5 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    seq (coe v8)
                    (case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> case coe v3 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                -> case coe v4 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                       -> let v15
                                                = coe
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                    erased
                                                    (\ v15 ->
                                                       coe
                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                         (coe v7))
                                                    (coe
                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                       (coe v7) (coe v1)) in
                                          coe
                                            (case coe v15 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                 -> if coe v16
                                                      then coe seq (coe v17) (coe v14)
                                                      else coe
                                                             seq (coe v17)
                                                             (coe
                                                                du_tailAt'45'all_376 (coe v6)
                                                                (coe v1) (coe v10) (coe v12)
                                                                (coe v14))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DefEnv._.found
d_found_454 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 -> ()) ->
  (MAlonzo.Code.Once.Type.T_PolyType_254 ->
   AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_found_454 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 ~v16 v17 ~v18 ~v19
  = du_found_454 v17
du_found_454 :: AgdaAny -> AgdaAny
du_found_454 v0 = coe v0
-- Once.Denotation.DefEnv.ImpEnvOf
d_ImpEnvOf_488 ::
  (MAlonzo.Code.Once.Type.T_Type_108 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_ImpEnvOf_488 = erased
-- Once.Denotation.DefEnv.impAt-found
d_impAt'45'found_504 ::
  (MAlonzo.Code.Once.Type.T_Type_108 -> ()) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_impAt'45'found_504 ~v0 ~v1 ~v2 ~v3 v4 = du_impAt'45'found_504 v4
du_impAt'45'found_504 :: AgdaAny -> AgdaAny
du_impAt'45'found_504 v0 = coe v0
-- Once.Denotation.DefEnv.impAt
d_impAt_516 ::
  (MAlonzo.Code.Once.Type.T_Type_108 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_impAt_516 ~v0 v1 v2 ~v3 v4 ~v5 = du_impAt_516 v1 v2 v4
du_impAt_516 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
du_impAt_516 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> let v9
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v9 ->
                                      coe
                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                        (coe v5))
                                   (coe
                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v5)
                                      (coe v1)) in
                         coe
                           (case coe v9 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                -> if coe v10
                                     then coe seq (coe v11) (coe v7)
                                     else coe
                                            seq (coe v11)
                                            (coe du_impAt_516 (coe v4) (coe v1) (coe v8))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
