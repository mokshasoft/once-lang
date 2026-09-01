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

module MAlonzo.Code.Once.Adequacy.CanonPolyTransport where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Adequacy.CanonPreserveMutual
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.CanonPolyTransport.canonPolysCtx
d_canonPolysCtx_6 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_canonPolysCtx_6 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v7))))
                           (coe d_canonPolysCtx_6 (coe v0) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport.canon-entry
d_canon'45'entry_20 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_canon'45'entry_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport.lookupPoly-canon
d_lookupPoly'45'canon_34 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupPoly'45'canon_34 = erased
-- Once.Adequacy.CanonPolyTransport.removePoly-canon
d_removePoly'45'canon_86 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_removePoly'45'canon_86 = erased
-- Once.Adequacy.CanonPolyTransport.lookupPoly-canon-just
d_lookupPoly'45'canon'45'just_144 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupPoly'45'canon'45'just_144 = erased
-- Once.Adequacy.CanonPolyTransport.PInB
d_PInB_166 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d_PInB_166 = erased
-- Once.Adequacy.CanonPolyTransport.lookupPoly-removePoly-mono
d_lookupPoly'45'removePoly'45'mono_188 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPoly'45'removePoly'45'mono_188 v0 v1 v2 v3 v4
  = case coe v2 of
      (:) v5 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    seq (coe v8)
                    (let v9
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v9 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v7))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v7)
                                  (coe v0)) in
                     coe
                       (case coe v9 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                            -> if coe v10
                                 then coe
                                        seq (coe v11)
                                        (let v12
                                               = coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                   erased
                                                   (\ v12 ->
                                                      coe
                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                        (coe v7))
                                                   (coe
                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                      (coe v7) (coe v1)) in
                                         coe
                                           (case coe v12 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                -> if coe v13
                                                     then coe
                                                            seq (coe v14)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v8) erased)
                                                     else coe
                                                            seq (coe v14)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v3) (coe v4))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 else coe
                                        seq (coe v11)
                                        (let v12
                                               = coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                   erased
                                                   (\ v12 ->
                                                      coe
                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                        (coe v7))
                                                   (coe
                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                      (coe v7) (coe v1)) in
                                         coe
                                           (case coe v12 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                -> if coe v13
                                                     then coe
                                                            seq (coe v14)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v8) erased)
                                                     else coe
                                                            seq (coe v14)
                                                            (coe
                                                               d_lookupPoly'45'removePoly'45'mono_188
                                                               (coe v0) (coe v1) (coe v6) (coe v3)
                                                               erased)
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport.removePoly-PInB
d_removePoly'45'PInB_310 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_removePoly'45'PInB_310 = erased
-- Once.Adequacy.CanonPolyTransport.canon-prefix-entry
d_canon'45'prefix'45'entry_338 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_canon'45'prefix'45'entry_338 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4))
                       (coe d_canonPolysCtx_6 (coe v0) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport.lookupPolyPrefix-canon
d_lookupPolyPrefix'45'canon_354 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupPolyPrefix'45'canon_354 = erased
-- Once.Adequacy.CanonPolyTransport.lookupPolyPrefix-canon-just
d_lookupPolyPrefix'45'canon'45'just_412 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupPolyPrefix'45'canon'45'just_412 = erased
-- Once.Adequacy.CanonPolyTransport.lookupPolyPrefix-mono
d_lookupPolyPrefix'45'mono_452 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPolyPrefix'45'mono_452 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
  = du_lookupPolyPrefix'45'mono_452 v0 v1 v2 v3 v4 v6
du_lookupPolyPrefix'45'mono_452 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lookupPolyPrefix'45'mono_452 v0 v1 v2 v3 v4 v5
  = case coe v2 of
      (:) v6 v7
        -> case coe v6 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    seq (coe v9)
                    (let v10
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v10 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v8))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v8)
                                  (coe v0)) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                            -> if coe v11
                                 then coe
                                        seq (coe v12)
                                        (coe
                                           du_aux_510 (coe v8) (coe v1) (coe v3) (coe v4) (coe v5)
                                           erased)
                                 else coe
                                        seq (coe v12)
                                        (let v13
                                               = coe
                                                   du_lookupPolyPrefix'45'mono_452 (coe v0) (coe v1)
                                                   (coe v7) (coe v3) (coe v4) (coe v5) in
                                         coe
                                           (coe
                                              seq (coe v13)
                                              (let v14
                                                     = coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                         erased
                                                         (\ v14 ->
                                                            coe
                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                              (coe v8))
                                                         (coe
                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                            (coe v8) (coe v1)) in
                                               coe
                                                 (case coe v14 of
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                      -> if coe v15
                                                           then coe
                                                                  seq (coe v16)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe v9) erased)
                                                           else coe seq (coe v16) (coe v13)
                                                    _ -> MAlonzo.RTE.mazUnreachableError))))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport._.aux
d_aux_510 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_aux_510 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 v13
          v14 ~v15 v16 ~v17 v18
  = du_aux_510 v1 v3 v13 v14 v16 v18
du_aux_510 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_aux_510 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v6 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                 (coe v1)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> if coe v7
                then coe
                       seq (coe v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
                          erased)
                else coe
                       seq (coe v8)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v5))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonPolyTransport.lookupPolyPrefix-PInB
d_lookupPolyPrefix'45'PInB_612 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupPolyPrefix'45'PInB_612 = erased
-- Once.Adequacy.CanonPolyTransport.cpc
d_cpc_644 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338
d_cpc_644 v0 v1
  = coe
      MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v1))
      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v1))
      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v1))
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v1))
      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v1))
      (coe
         d_canonPolysCtx_6 (coe v0)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364 (coe v1)))
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_sigEffects_366 (coe v1))
-- Once.Adequacy.CanonPolyTransport.composeArgB-lookup-polys-canon
d_composeArgB'45'lookup'45'polys'45'canon_658 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composeArgB'45'lookup'45'polys'45'canon_658 = erased
-- Once.Adequacy.CanonPolyTransport.composeArgB-fst-polys-canon
d_composeArgB'45'fst'45'polys'45'canon_700 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composeArgB'45'fst'45'polys'45'canon_700 = erased
-- Once.Adequacy.CanonPolyTransport.composeArgB-snd-polys-canon
d_composeArgB'45'snd'45'polys'45'canon_770 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composeArgB'45'snd'45'polys'45'canon_770 = erased
-- Once.Adequacy.CanonPolyTransport.composeArgB-rvar-polys-canon
d_composeArgB'45'rvar'45'polys'45'canon_842 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composeArgB'45'rvar'45'polys'45'canon_842 = erased
-- Once.Adequacy.CanonPolyTransport.composeArgB-polys-canon
d_composeArgB'45'polys'45'canon_940 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composeArgB'45'polys'45'canon_940 = erased
-- Once.Adequacy.CanonPolyTransport.domainOfHead-polys-canon
d_domainOfHead'45'polys'45'canon_1576 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_domainOfHead'45'polys'45'canon_1576 = erased
-- Once.Adequacy.CanonPolyTransport.composeMid-polys-canon
d_composeMid'45'polys'45'canon_1720 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composeMid'45'polys'45'canon_1720 = erased
-- Once.Adequacy.CanonPolyTransport.polys-transport-ᵢ
d_polys'45'transport'45''7522'_1764 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_polys'45'transport'45''7522'_1764 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
                                    v10 v11 v12 v13
  = du_polys'45'transport'45''7522'_1764
      v0 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13
du_polys'45'transport'45''7522'_1764 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_polys'45'transport'45''7522'_1764 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_22
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_22
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_34
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_34
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_40
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_40
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_44
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_44
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_48
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_48
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_60 v16
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_60 v16
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_70 v17
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_70 v17
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v16
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v16
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_86 v18
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_86 v18
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_102 v15 v16 v17 v18 v24 v26
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_102
             v15
             (MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346
                (coe v0) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v16))
             (d_canonPolysCtx_6 (coe v0) (coe v17)) v18 v24
             (coe
                du_polys'45'transport'45''7580'_1788 (coe v0) (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                (coe (0 :: Integer)) (coe v5)
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptySigEffects_12)
                (coe v17)
                (coe
                   MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v16))
                (coe v9)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                         (coe v5) (coe d_canonPolysCtx_6 (coe v0) (coe v17)))))
                (coe
                   MAlonzo.Code.Once.Adequacy.CanonPreserveMutual.du_canon'45'pres'45''7580'_116
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                      (coe v5) (coe v17))
                   (coe v16) (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                         (coe
                            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                            (coe v5) (coe d_canonPolysCtx_6 (coe v0) (coe v17)))))
                   (coe v0) (coe v26)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_112 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_112
                    (coe
                       du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v17) (coe v9)
                       (coe v10) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_128 v17 v18 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v21 v22
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v23 v24
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_128 v17 v18
                           (coe
                              du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v21) (coe v23)
                              (coe v17) (coe v19))
                           (coe
                              du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22) (coe v24)
                              (coe v18) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136 v15
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_148
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_148
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_168 v16 v18 v19 v20 v21 v22
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v23 v24 v25
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_168 v16 v18 v19 v20
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v24) (coe v16)
                       (coe v19) (coe v21))
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                          (coe v23) (coe v16))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v3) (coe v16))
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v25) (coe v9)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v18 v20)
                       (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_198 v18 v19 v21 v22 v23 v24 v25 v26 v27 v28
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v29 v30 v31 v32 v33
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_198 v18 v19 v21
                    v22 v23 v24 v25
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v29)
                       (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v18) (coe v19))
                       (coe v23) (coe v26))
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                          (coe v30) (coe v18))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v3) (coe v18))
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v31) (coe v9)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v21 v24)
                       (coe v27))
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                          (coe v32) (coe v19))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v3) (coe v19))
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v33) (coe v9)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v22 v25)
                       (coe v28))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212 v16
                    v17
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v16) (coe v19))
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226
                    v16 v17
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v16) (coe v19))
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240
                    v16 v17
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v16) (coe v19))
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254
                    v16 v17
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v16) (coe v19))
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268 v16
                    v17
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v16) (coe v19))
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278 v15 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278 v15
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v18) (coe v9)
                       (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290 v15 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290 v15 v16
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v9) (coe v15))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302 v14 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302 v14 v16
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v14) (coe v9))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_312 v14 v15 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_312 v14
                    v15
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v18) (coe v14)
                       (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324 v14 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324
                    v14 v16
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__122
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v9))
                          (coe v14))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v15 v17 v18 v19 v21 v22
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v15 v17 v18 v19
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v17)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v9))
                       (coe v18) (coe v21))
                    (coe
                       du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v24) (coe v15)
                       (coe v19) (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v15 v17 v18 v20 v21
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v24 v25 v26
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v15 v17 v18
                           (coe
                              du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v26))
                              (coe v17) (coe v20))
                           (coe
                              du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23) (coe v15)
                              (coe v18) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport.polys-transport-ᶜ
d_polys'45'transport'45''7580'_1788 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_polys'45'transport'45''7580'_1788 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
                                    v10 v11 v12 v13
  = du_polys'45'transport'45''7580'_1788
      v0 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13
du_polys'45'transport'45''7580'_1788 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_polys'45'transport'45''7580'_1788 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_366
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_366
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_376
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_376
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_386
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_386
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_394
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_394
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_402
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_402
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_412
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_412
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_422
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_422
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check_442 v16 v19 v20 v22 v23
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v24 v25
               -> case coe v24 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v26 v27
                      -> case coe v9 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v28 v29 v30
                             -> case coe v29 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v31 v32
                                    -> coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check_442
                                         v16 v19 v20
                                         (coe
                                            du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1)
                                            (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                            (coe v27)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v16)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v32))
                                               (coe v30))
                                            (coe v19) (coe v22))
                                         (coe
                                            du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1)
                                            (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                            (coe v25)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v28)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v32))
                                               (coe v16))
                                            (coe v20) (coe v23))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_462 v19 v20 v21 v22
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
               -> case coe v23 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v25 v26
                      -> case coe v9 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v27 v28 v29
                             -> case coe v27 of
                                  MAlonzo.Code.Once.Type.C__'43'__124 v30 v31
                                    -> case coe v28 of
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 v32 v33
                                           -> coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_462
                                                v19 v20
                                                (coe
                                                   du_polys'45'transport'45''7580'_1788 (coe v0)
                                                   (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                                   (coe v6) (coe v7) (coe v26)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                      (coe v30)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v33))
                                                      (coe v29))
                                                   (coe v19) (coe v21))
                                                (coe
                                                   du_polys'45'transport'45''7580'_1788 (coe v0)
                                                   (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                                                   (coe v6) (coe v7) (coe v24)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                      (coe v31)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v33))
                                                      (coe v29))
                                                   (coe v20) (coe v22))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_480 v18 v19 v20 v21
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
               -> case coe v22 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v24 v25
                      -> case coe v9 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v26 v27 v28
                             -> case coe v28 of
                                  MAlonzo.Code.Once.Type.C__'42'__122 v29 v30
                                    -> coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_480
                                         v18 v19
                                         (coe
                                            du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1)
                                            (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                            (coe v25)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v26)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_pure_34))
                                               (coe v29))
                                            (coe v18) (coe v20))
                                         (coe
                                            du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1)
                                            (coe v2) (coe v3) (coe v4) (coe v5) (coe v6) (coe v7)
                                            (coe v23)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v26)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_pure_34))
                                               (coe v30))
                                            (coe v19) (coe v21))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_494 v18
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v21 v22 v23
                      -> case coe v23 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v24 v25 v26
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_494
                                  (coe
                                     du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                                     (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v20)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122 (coe v21) (coe v24))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                           (coe MAlonzo.Code.Once.Type.C_pure_34))
                                        (coe v26))
                                     (coe v10) (coe v18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_506 v17 v18
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v21 v22 v23
                      -> case coe v21 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v24
                             -> case coe v22 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                                    -> coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_506
                                         v17
                                         (coe
                                            du_polys'45'transport'45''7580'_1788 (coe v0)
                                            (coe (0 :: Integer))
                                            (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                                            (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                            (coe (0 :: Integer)) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_emptySigEffects_12)
                                            (coe v7) (coe v20)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe
                                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                  (coe v24) (coe v23))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v26))
                                               (coe v23))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                                     (coe v5)
                                                     (coe d_canonPolysCtx_6 (coe v0) (coe v7)))))
                                            (coe v18))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516 v16
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516
             (coe
                du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                (coe v10) (coe v16))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_534 v18 v21
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v22 v23
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v24 v25 v26
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_534 v18
                           (coe
                              du_polys'45'transport'45''7580'_1788 (coe v0)
                              (coe addInt (coe (1 :: Integer)) (coe v1))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                                 (coe v22) (coe v24))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v3) (coe v24))
                              (coe v4) (coe v5) (coe v6) (coe v7) (coe v23) (coe v26)
                              (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v18 v10)
                              (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_550 v17 v18 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v21 v22
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v23 v24
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_550
                           v17 v18
                           (coe
                              du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v21) (coe v23)
                              (coe v17) (coe v19))
                           (coe
                              du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22) (coe v24)
                              (coe v18) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_560 v15 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v20
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_560
                           v15 v16
                           (coe
                              du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v20) (coe v9))
                              (coe v15) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_572 v14 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_572 v14
                    v16
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__122
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v9))
                          (coe v14))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_584 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v20 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_584
                           v16
                           (coe
                              du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19) (coe v20)
                              (coe v16) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_596 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v20 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_596
                           v16
                           (coe
                              du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19) (coe v21)
                              (coe v16) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_606 v15 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_606
                    v15
                    (coe
                       du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v18)
                       (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618 v17
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618
                    (coe
                       du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v18)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v20))
                       (coe v10) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_634 v15 v17 v18 v20 v21
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_634
                    v15 v17 v18
                    (coe
                       du_polys'45'transport'45''7522'_1764 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23) (coe v15)
                       (coe v18) (coe v20))
                    (coe
                       du_polys'45'transport'45''7580'_1788 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v9))
                       (coe v17) (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_648 v15 v16 v17 v24
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_648
             v15
             (MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346
                (coe v0) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v16))
             (d_canonPolysCtx_6 (coe v0) (coe v17))
             (coe
                du_polys'45'transport'45''7580'_1788 (coe v0) (coe (0 :: Integer))
                (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                (coe (0 :: Integer)) (coe v5)
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptySigEffects_12)
                (coe v17)
                (coe
                   MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v16))
                (coe v9)
                (coe
                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                         (coe v5) (coe d_canonPolysCtx_6 (coe v0) (coe v17)))))
                (coe
                   MAlonzo.Code.Once.Adequacy.CanonPreserveMutual.du_canon'45'pres'45''7580'_116
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                      (coe v5) (coe v17))
                   (coe v16) (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                      (coe
                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                         (coe
                            MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                            (coe v5) (coe d_canonPolysCtx_6 (coe v0) (coe v17)))))
                   (coe v0) (coe v24)))
      _ -> MAlonzo.RTE.mazUnreachableError
