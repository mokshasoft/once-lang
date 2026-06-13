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

module MAlonzo.Code.Once.Verified.SourceSemantics where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Once.Verified.Trace
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Verified.SourceSemantics.BTag
d_BTag_6 = ()
data T_BTag_6
  = C_bId_8 | C_bFst_10 | C_bSnd_12 | C_bInl_14 | C_bInr_16 |
    C_bIn_18 | C_bOut_20 | C_bCompose_22 | C_bCase_24 | C_bCata_26 |
    C_bTerminal_28
-- Once.Verified.SourceSemantics.Value
d_Value_30 = ()
data T_Value_30
  = C_Vint_32 Integer |
    C_Vstr_34 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_Vunit_36 | C_Vpair_38 T_Value_30 T_Value_30 |
    C_Vinl_40 T_Value_30 | C_Vinr_42 T_Value_30 | C_Vin_44 T_Value_30 |
    C_Vclos_46 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
               MAlonzo.Code.Agda.Builtin.String.T_String_6
               MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 |
    C_Vbuiltin_48 T_BTag_6 [T_Value_30] |
    C_Vsigop_50 MAlonzo.Code.Agda.Builtin.String.T_String_6
                [T_Value_30]
-- Once.Verified.SourceSemantics.Env
d_Env_52 :: ()
d_Env_52 = erased
-- Once.Verified.SourceSemantics.Result
d_Result_54 :: ()
d_Result_54 = erased
-- Once.Verified.SourceSemantics.lookupEnv
d_lookupEnv_56 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe T_Value_30
d_lookupEnv_56 v0 v1
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
                                 (coe v1))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_lookupEnv_56 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceSemantics.argℕ
d_argℕ_86 :: T_Value_30 -> Maybe Integer
d_argℕ_86 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_Vint_32 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2))
         _ -> coe v1)
-- Once.Verified.SourceSemantics._>>=ᵣ_
d__'62''62''61''7523'__90 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (T_Value_30 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'62''62''61''7523'__90 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> let v5 = coe v1 v3 in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                         -> case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                        (coe
                                           MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                                           (coe v8)))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceSemantics.prependEv
d_prependEv_118 ::
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prependEv_118 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceSemantics.divℤ
d_divℤ_126
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.SourceSemantics.div\8484"
-- Once.Verified.SourceSemantics.modℤ
d_modℤ_128
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Verified.SourceSemantics.mod\8484"
-- Once.Verified.SourceSemantics.boolToSum
d_boolToSum_130 :: Bool -> T_Value_30
d_boolToSum_130 v0
  = if coe v0
      then coe C_Vinl_40 (coe C_Vunit_36)
      else coe C_Vinr_42 (coe C_Vunit_36)
-- Once.Verified.SourceSemantics.binResult
d_binResult_132 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  T_Value_30 ->
  T_Value_30 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_binResult_132 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
           -> case coe v1 of
                C_Vint_32 v4
                  -> case coe v2 of
                       C_Vint_32 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    C_Vint_32
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v4)
                                       (coe v5)))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
           -> case coe v1 of
                C_Vint_32 v4
                  -> case coe v2 of
                       C_Vint_32 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    C_Vint_32
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v4)
                                       (coe v5)))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
           -> case coe v1 of
                C_Vint_32 v4
                  -> case coe v2 of
                       C_Vint_32 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    C_Vint_32
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v4)
                                       (coe v5)))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
           -> case coe v1 of
                C_Vint_32 v4
                  -> case coe v2 of
                       C_Vint_32 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe C_Vint_32 (coe d_divℤ_126 v4 v5))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
           -> case coe v1 of
                C_Vint_32 v4
                  -> case coe v2 of
                       C_Vint_32 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe C_Vint_32 (coe d_modℤ_128 v4 v5))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
           -> case coe v1 of
                C_Vint_32 v4
                  -> case coe v2 of
                       C_Vint_32 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    d_boolToSum_130
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.d_not_22
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
                                          (coe v5) (coe v4))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
           -> case coe v1 of
                C_Vint_32 v4
                  -> case coe v2 of
                       C_Vint_32 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    d_boolToSum_130
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110 (coe v4)
                                       (coe v5)))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
           -> case coe v1 of
                C_Vint_32 v4
                  -> case coe v2 of
                       C_Vint_32 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    d_boolToSum_130
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.d_not_22
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
                                          (coe v4) (coe v5))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
           -> case coe v1 of
                C_Vint_32 v4
                  -> case coe v2 of
                       C_Vint_32 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    d_boolToSum_130
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110 (coe v5)
                                       (coe v4)))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
           -> case coe v1 of
                C_Vint_32 v4
                  -> case coe v2 of
                       C_Vint_32 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    d_boolToSum_130
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                       (coe
                                          MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
                                          (coe v4) (coe v5))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
           -> case coe v1 of
                C_Vint_32 v4
                  -> case coe v2 of
                       C_Vint_32 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    d_boolToSum_130
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.d_not_22
                                       (coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                          (coe
                                             MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
                                             (coe v4) (coe v5)))))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       _ -> coe v3
                _ -> coe v3
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.SourceSemantics.btable
d_btable_178 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_btable_178
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe ("id" :: Data.Text.Text)) (coe C_bId_8))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe ("fst" :: Data.Text.Text)) (coe C_bFst_10))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
               (coe ("snd" :: Data.Text.Text)) (coe C_bSnd_12))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe ("inl" :: Data.Text.Text)) (coe C_bInl_14))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe ("inr" :: Data.Text.Text)) (coe C_bInr_16))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe ("In" :: Data.Text.Text)) (coe C_bIn_18))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe ("Out" :: Data.Text.Text)) (coe C_bOut_20))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe ("compose" :: Data.Text.Text)) (coe C_bCompose_22))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe ("case" :: Data.Text.Text)) (coe C_bCase_24))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe ("cata" :: Data.Text.Text)) (coe C_bCata_26))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe ("terminal" :: Data.Text.Text)) (coe C_bTerminal_28))
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))
-- Once.Verified.SourceSemantics.classifyB
d_classifyB_180 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe T_BTag_6
d_classifyB_180 v0 = coe d_go_188 (coe v0) (coe d_btable_178)
-- Once.Verified.SourceSemantics._.go
d_go_188 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Maybe T_BTag_6
d_go_188 v0 v1
  = case coe v1 of
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
                                 (coe v0))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_go_188 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceSemantics.resolveName
d_resolveName_212 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_Value_30
d_resolveName_212 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v1 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                 (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                 (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
                 (coe
                    MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                    ("id" :: Data.Text.Text))) in
    coe
      (let v2 = coe C_bId_8 in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe ("fst" :: Data.Text.Text)) (coe C_bFst_10))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe ("snd" :: Data.Text.Text)) (coe C_bSnd_12))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe ("inl" :: Data.Text.Text)) (coe C_bInl_14))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe ("inr" :: Data.Text.Text)) (coe C_bInr_16))
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe ("In" :: Data.Text.Text)) (coe C_bIn_18))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe ("Out" :: Data.Text.Text)) (coe C_bOut_20))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe ("compose" :: Data.Text.Text)) (coe C_bCompose_22))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe ("case" :: Data.Text.Text)) (coe C_bCase_24))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe ("cata" :: Data.Text.Text)) (coe C_bCata_26))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe ("terminal" :: Data.Text.Text))
                                                  (coe C_bTerminal_28))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))) in
          coe
            (case coe v1 of
               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                 -> if coe v4
                      then let v6
                                 = seq
                                     (coe v5)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)) in
                           coe
                             (case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                  -> coe
                                       C_Vbuiltin_48 (coe v7)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> coe
                                       C_Vsigop_50 (coe v0)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      else (let v6 = seq (coe v5) (coe d_go_188 (coe v0) (coe v3)) in
                            coe
                              (case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                   -> coe
                                        C_Vbuiltin_48 (coe v7)
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe
                                        C_Vsigop_50 (coe v0)
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 _ -> MAlonzo.RTE.mazUnreachableError))
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Verified.SourceSemantics.Defs
d_Defs_226 :: ()
d_Defs_226 = erased
-- Once.Verified.SourceSemantics.extractDefs
d_extractDefs_228 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extractDefs_228 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = d_extractDefs_228 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_36 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v6))
                       (coe d_extractDefs_228 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceSemantics.lookupDef
d_lookupDef_238 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_lookupDef_238 v0 v1
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
                                 (coe v1))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_lookupDef_238 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceSemantics.eval
d_eval_268 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval_268 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v5
                  -> let v6 = d_lookupEnv_56 (coe v2) (coe v5) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> let v7 = d_lookupDef_238 (coe v1) (coe v5) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                      -> coe
                                           d_eval_268 (coe v4) (coe v1)
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                           (coe v8)
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe d_resolveName_212 (coe v5))
                                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             C_Vsigop_50 (coe v5)
                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v5 v6
                  -> coe
                       d__'62''62''61''7523'__90
                       (coe d_eval_268 (coe v4) (coe v1) (coe v2) (coe v5))
                       (coe
                          (\ v7 ->
                             d__'62''62''61''7523'__90
                               (coe d_eval_268 (coe v4) (coe v1) (coe v2) (coe v6))
                               (coe d_apply_270 (coe v4) (coe v1) (coe v7))))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe C_Vclos_46 (coe v2) (coe v5) (coe v6))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v5 v6 v7
                  -> coe
                       d__'62''62''61''7523'__90
                       (coe d_eval_268 (coe v4) (coe v1) (coe v2) (coe v6))
                       (coe
                          (\ v8 ->
                             d_eval_268
                               (coe v4) (coe v1)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v8))
                                  (coe v2))
                               (coe v7)))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v5 v6
                  -> coe
                       d__'62''62''61''7523'__90
                       (coe d_eval_268 (coe v4) (coe v1) (coe v2) (coe v5))
                       (coe
                          (\ v7 ->
                             d__'62''62''61''7523'__90
                               (coe d_eval_268 (coe v4) (coe v1) (coe v2) (coe v6))
                               (coe
                                  (\ v8 ->
                                     coe
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe C_Vpair_38 (coe v7) (coe v8))
                                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v5 v6 v7 v8 v9
                  -> let v10 = d_eval_268 (coe v4) (coe v1) (coe v2) (coe v5) in
                     coe
                       (case coe v10 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                            -> case coe v11 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> case coe v12 of
                                        C_Vinl_40 v14
                                          -> coe
                                               d_prependEv_118 (coe v13)
                                               (coe
                                                  d_eval_268 (coe v4) (coe v1)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v6) (coe v14))
                                                     (coe v2))
                                                  (coe v7))
                                        C_Vinr_42 v14
                                          -> coe
                                               d_prependEv_118 (coe v13)
                                               (coe
                                                  d_eval_268 (coe v4) (coe v1)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v8) (coe v14))
                                                     (coe v2))
                                                  (coe v9))
                                        _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v10
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_Vunit_36)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe C_Vint_32 (coe v5))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe C_Vstr_34 (coe v5))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v5 v6
                  -> coe d_eval_268 (coe v4) (coe v1) (coe v2) (coe v5)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v5 v6 v7
                  -> coe
                       d__'62''62''61''7523'__90
                       (coe d_eval_268 (coe v4) (coe v1) (coe v2) (coe v6))
                       (coe
                          (\ v8 ->
                             d__'62''62''61''7523'__90
                               (coe d_eval_268 (coe v4) (coe v1) (coe v2) (coe v7))
                               (coe d_binResult_132 (coe v5) (coe v8))))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v6
                  -> coe
                       d__'62''62''61''7523'__90
                       (coe d_eval_268 (coe v4) (coe v1) (coe v2) (coe v6))
                       (coe du_neg_540)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.SourceSemantics.apply
d_apply_270 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Value_30 ->
  T_Value_30 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_apply_270 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v5 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
              coe
                (case coe v2 of
                   C_Vclos_46 v6 v7 v8
                     -> coe
                          d_eval_268 (coe v4) (coe v1)
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v3))
                             (coe v6))
                          (coe v8)
                   C_Vbuiltin_48 v6 v7
                     -> coe
                          d_applyBuiltin_272 (coe v4) (coe v1) (coe v6)
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                   C_Vsigop_50 v6 v7
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_Vunit_36)
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                (coe
                                   MAlonzo.Code.Once.Verified.Trace.C_mk'45'event_146 (coe v6)
                                   (coe d_argℕ_86 (coe v3)))
                                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                   _ -> coe v5))
-- Once.Verified.SourceSemantics.applyBuiltin
d_applyBuiltin_272 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_BTag_6 ->
  [T_Value_30] -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_applyBuiltin_272 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe C_Vbuiltin_48 (coe v2) (coe v3))
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)) in
    coe
      (case coe v2 of
         C_bId_8
           -> case coe v3 of
                (:) v5 v6
                  -> case coe v6 of
                       []
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6))
                       _ -> coe v4
                _ -> coe v4
         C_bFst_10
           -> case coe v3 of
                (:) v5 v6
                  -> case coe v5 of
                       C_Vpair_38 v7 v8
                         -> case coe v6 of
                              []
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                        (coe v6))
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         C_bSnd_12
           -> case coe v3 of
                (:) v5 v6
                  -> case coe v5 of
                       C_Vpair_38 v7 v8
                         -> case coe v6 of
                              []
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                        (coe v6))
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         C_bInl_14
           -> case coe v3 of
                (:) v5 v6
                  -> case coe v6 of
                       []
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe C_Vinl_40 (coe v5)) (coe v6))
                       _ -> coe v4
                _ -> coe v4
         C_bInr_16
           -> case coe v3 of
                (:) v5 v6
                  -> case coe v6 of
                       []
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe C_Vinr_42 (coe v5)) (coe v6))
                       _ -> coe v4
                _ -> coe v4
         C_bIn_18
           -> case coe v3 of
                (:) v5 v6
                  -> case coe v6 of
                       []
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_Vin_44 (coe v5))
                                 (coe v6))
                       _ -> coe v4
                _ -> coe v4
         C_bOut_20
           -> case coe v3 of
                (:) v5 v6
                  -> case coe v5 of
                       C_Vin_44 v7
                         -> case coe v6 of
                              []
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                        (coe v6))
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         C_bCompose_22
           -> case coe v3 of
                (:) v5 v6
                  -> case coe v6 of
                       (:) v7 v8
                         -> case coe v8 of
                              (:) v9 v10
                                -> case coe v10 of
                                     []
                                       -> coe
                                            d__'62''62''61''7523'__90
                                            (coe d_apply_270 (coe v0) (coe v1) (coe v7) (coe v9))
                                            (coe d_apply_270 (coe v0) (coe v1) (coe v5))
                                     _ -> coe v4
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         C_bCase_24
           -> case coe v3 of
                (:) v5 v6
                  -> case coe v6 of
                       (:) v7 v8
                         -> case coe v8 of
                              (:) v9 v10
                                -> case coe v9 of
                                     C_Vinl_40 v11
                                       -> case coe v10 of
                                            []
                                              -> coe
                                                   d_apply_270 (coe v0) (coe v1) (coe v5) (coe v11)
                                            _ -> coe v4
                                     C_Vinr_42 v11
                                       -> case coe v10 of
                                            []
                                              -> coe
                                                   d_apply_270 (coe v0) (coe v1) (coe v7) (coe v11)
                                            _ -> coe v4
                                     _ -> coe v4
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         C_bCata_26
           -> case coe v3 of
                (:) v5 v6
                  -> case coe v6 of
                       (:) v7 v8
                         -> case coe v8 of
                              [] -> coe d_cataFold_274 (coe v0) (coe v1) (coe v5) (coe v7)
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         C_bTerminal_28
           -> case coe v3 of
                (:) v5 v6
                  -> case coe v6 of
                       []
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_Vunit_36)
                                 (coe v6))
                       _ -> coe v4
                _ -> coe v4
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Verified.SourceSemantics.cataFold
d_cataFold_274 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Value_30 ->
  T_Value_30 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cataFold_274 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v5 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
              coe
                (case coe v3 of
                   C_Vin_44 v6
                     -> coe
                          d__'62''62''61''7523'__90
                          (coe d_mapIn_276 (coe v4) (coe v1) (coe v2) (coe v6))
                          (coe d_apply_270 (coe v4) (coe v1) (coe v2))
                   _ -> coe v5))
-- Once.Verified.SourceSemantics.mapIn
d_mapIn_276 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Value_30 ->
  T_Value_30 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mapIn_276 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v5
                    = coe
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)) in
              coe
                (case coe v3 of
                   C_Vpair_38 v6 v7
                     -> coe
                          d__'62''62''61''7523'__90
                          (coe d_mapIn_276 (coe v4) (coe v1) (coe v2) (coe v6))
                          (coe
                             (\ v8 ->
                                d__'62''62''61''7523'__90
                                  (coe d_mapIn_276 (coe v4) (coe v1) (coe v2) (coe v7))
                                  (coe
                                     (\ v9 ->
                                        coe
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe C_Vpair_38 (coe v8) (coe v9))
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                   C_Vinl_40 v6
                     -> coe
                          d__'62''62''61''7523'__90
                          (coe d_mapIn_276 (coe v4) (coe v1) (coe v2) (coe v6))
                          (coe
                             (\ v7 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe C_Vinl_40 (coe v7))
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                   C_Vinr_42 v6
                     -> coe
                          d__'62''62''61''7523'__90
                          (coe d_mapIn_276 (coe v4) (coe v1) (coe v2) (coe v6))
                          (coe
                             (\ v7 ->
                                coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe C_Vinr_42 (coe v7))
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                   C_Vin_44 v6
                     -> coe d_cataFold_274 (coe v4) (coe v1) (coe v2) (coe v3)
                   _ -> coe v5))
-- Once.Verified.SourceSemantics._.neg
d_neg_540 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_Value_30 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_neg_540 ~v0 ~v1 ~v2 ~v3 v4 = du_neg_540 v4
du_neg_540 ::
  T_Value_30 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_neg_540 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         C_Vint_32 v2
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      C_Vint_32
                      (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v2)))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         _ -> coe v1)
-- Once.Verified.SourceSemantics.runTraceEval
d_runTraceEval_740 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_runTraceEval_740 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3 -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceSemantics.runTraceMain
d_runTraceMain_744 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_runTraceMain_744 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> coe
             d_runTraceEval_740
             (coe
                d_eval_268 (coe v0) (coe v1)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceSemantics.runTrace
d_runTrace_756 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_136]
d_runTrace_756 v0 v1
  = coe
      d_runTraceMain_744 (coe v1)
      (coe
         d_extractDefs_228
         (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
      (coe
         d_lookupDef_238
         (coe
            d_extractDefs_228
            (coe MAlonzo.Code.Once.Parser.Module.Core.d_decls_48 (coe v0)))
         (coe ("main" :: Data.Text.Text)))
-- Once.Verified.SourceSemantics.runTrace-no-main
d_runTrace'45'no'45'main_768 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_runTrace'45'no'45'main_768 = erased
