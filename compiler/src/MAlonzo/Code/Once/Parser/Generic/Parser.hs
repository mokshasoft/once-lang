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

module MAlonzo.Code.Once.Parser.Generic.Parser where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.Generic.Parser.Res<
d_Res'60'_8 :: () -> Integer -> ()
d_Res'60'_8 = erased
-- Once.Parser.Generic.Parser.Res≤
d_Res'8804'_18 :: () -> Integer -> ()
d_Res'8804'_18 = erased
-- Once.Parser.Generic.Parser.forget<
d_forget'60'_32 ::
  () ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_forget'60'_32 ~v0 ~v1 v2 = du_forget'60'_32 v2
du_forget'60'_32 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_forget'60'_32 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.forget≤
d_forget'8804'_42 ::
  () ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_forget'8804'_42 ~v0 ~v1 v2 = du_forget'8804'_42 v2
du_forget'8804'_42 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_forget'8804'_42 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.under
d_under_54 ::
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_under_54 ~v0 v1 ~v2 v3 v4 = du_under_54 v1 v3 v4
du_under_54 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_under_54 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122 (coe v0)
                                    (coe v7) (coe v1))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.after<
d_after'60'_72 ::
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_after'60'_72 ~v0 ~v1 ~v2 v3 v4 = du_after'60'_72 v3 v4
du_after'60'_72 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_after'60'_72 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                    (coe v6) (coe v0))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.weaken
d_weaken_88 ::
  () ->
  Integer ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_weaken_88 ~v0 ~v1 v2 = du_weaken_88 v2
du_weaken_88 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_weaken_88 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                    (coe v5))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.mapRes
d_mapRes_102 ::
  () ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_mapRes_102 ~v0 ~v1 ~v2 v3 v4 = du_mapRes_102 v3 v4
du_mapRes_102 ::
  (AgdaAny -> AgdaAny) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_mapRes_102 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v3) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.AccT
d_AccT_114 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_AccT_114 = erased
-- Once.Parser.Generic.Parser.<3
d_'60'3_120 :: Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60'3_120 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
      (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220 (coe v0))
      (coe
         MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
         (coe addInt (coe (2 :: Integer)) (coe v0))
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
            (coe addInt (coe (1 :: Integer)) (coe v0)))
         (coe
            MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
            (coe addInt (coe (2 :: Integer)) (coe v0))))
-- Once.Parser.Generic.Parser.KwV
d_KwV_124 a0 = ()
data T_KwV_124
  = C_vUnit_126 | C_vVoid_128 | C_vInt_130 | C_vFloat_132 |
    C_vEff_134 | C_vAct_136 | C_vMu_138 | C_vNu_140 | C_vNone_144
-- Once.Parser.Generic.Parser.kwD
d_kwD_150 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_KwV_124 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_KwV_124 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> T_KwV_124
d_kwD_150 ~v0 v1 ~v2 v3 v4 = du_kwD_150 v1 v3 v4
du_kwD_150 ::
  T_KwV_124 ->
  T_KwV_124 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> T_KwV_124
du_kwD_150 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v0)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.kw
d_kw_170 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_KwV_124 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_KwV_124 -> T_KwV_124
d_kw_170 v0 v1 v2 v3
  = coe
      du_kwD_150 (coe v1) (coe v3)
      (coe
         MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v2)
         (coe v0))
-- Once.Parser.Generic.Parser.kwV
d_kwV_182 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_KwV_124
d_kwV_182 v0
  = coe
      d_kw_170 (coe ("Unit" :: Data.Text.Text)) (coe C_vUnit_126)
      (coe v0)
      (coe
         d_kw_170 (coe ("Void" :: Data.Text.Text)) (coe C_vVoid_128)
         (coe v0)
         (coe
            d_kw_170 (coe ("Int" :: Data.Text.Text)) (coe C_vInt_130) (coe v0)
            (coe
               d_kw_170 (coe ("Float" :: Data.Text.Text)) (coe C_vFloat_132)
               (coe v0)
               (coe
                  d_kw_170 (coe ("Eff" :: Data.Text.Text)) (coe C_vEff_134) (coe v0)
                  (coe
                     d_kw_170 (coe ("Act" :: Data.Text.Text)) (coe C_vAct_136) (coe v0)
                     (coe
                        d_kw_170 (coe ("Mu" :: Data.Text.Text)) (coe C_vMu_138) (coe v0)
                        (coe
                           d_kw_170 (coe ("Nu" :: Data.Text.Text)) (coe C_vNu_140) (coe v0)
                           (coe C_vNone_144))))))))
-- Once.Parser.Generic.Parser.FKwV
d_FKwV_186 a0 = ()
data T_FKwV_186 = C_fvId_188 | C_fvK_190 | C_fvNone_194
-- Once.Parser.Generic.Parser.fkwD
d_fkwD_200 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_FKwV_186 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_FKwV_186 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> T_FKwV_186
d_fkwD_200 ~v0 v1 ~v2 v3 v4 = du_fkwD_200 v1 v3 v4
du_fkwD_200 ::
  T_FKwV_186 ->
  T_FKwV_186 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> T_FKwV_186
du_fkwD_200 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v0)
             else coe seq (coe v4) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.fkwV
d_fkwV_218 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_FKwV_186
d_fkwV_218 v0
  = coe
      du_fkwD_200 (coe C_fvId_188)
      (coe
         du_fkwD_200 (coe C_fvK_190) (coe C_fvNone_194)
         (coe
            MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
            (coe ("K" :: Data.Text.Text))))
      (coe
         MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
         (coe ("Id" :: Data.Text.Text)))
-- Once.Parser.Generic.Parser.actD
d_actD_228 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_actD_228 ~v0 v1 v2 = du_actD_228 v1 v2
du_actD_228 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_actD_228 v0 v1
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then coe
                    seq (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) erased))
             else coe
                    seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.actHead?
d_actHead'63'_240 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_actHead'63'_240 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TLParen_16
                  -> case coe v3 of
                       (:) v4 v5
                         -> case coe v4 of
                              MAlonzo.Code.Once.Parser.Token.C_TWord_8 v6
                                -> coe
                                     du_actD_228 (coe v5)
                                     (coe
                                        MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v6)
                                        (coe ("Act" :: Data.Text.Text)))
                              _ -> coe v1
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Generic.Parser.HeadV
d_HeadV_246 a0 = ()
data T_HeadV_246 = C_hWord_252 | C_hParen_256 | C_hOther_260
-- Once.Parser.Generic.Parser.headV
d_headV_264 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_HeadV_246
d_headV_264 v0
  = let v1 = coe C_hOther_260 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4 -> coe C_hWord_252
                MAlonzo.Code.Once.Parser.Token.C_TLParen_16 -> coe C_hParen_256
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Generic.Parser.CloseV
d_CloseV_274 a0 = ()
data T_CloseV_274 = C_cR_278 | C_cOther_282
-- Once.Parser.Generic.Parser.closeV
d_closeV_286 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> T_CloseV_274
d_closeV_286 v0
  = let v1 = coe C_cOther_282 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TRParen_18 -> coe C_cR_278
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Generic.Parser.Make.nuC
d_nuC_366 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_CloseV_274 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuC_366 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_cR_278
        -> case coe v3 of
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_aNuAct_174 v0 v2)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                             (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                (coe
                                   addInt (coe (1 :: Integer))
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                      (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                                      (coe (0 :: Integer)) (coe v8)))
                                (coe
                                   MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                      (coe (\ v9 v10 -> addInt (coe (1 :: Integer)) (coe v10)))
                                      (coe (0 :: Integer)) (coe v8)))
                                (coe v4))
                             (coe
                                d_'60'3_120
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (let v9 = \ v9 -> addInt (coe (1 :: Integer)) (coe v9) in
                                    coe (coe (\ v10 -> v9)))
                                   (coe (0 :: Integer)) (coe v1))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cOther_282 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.nuClose
d_nuClose_386 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuClose_386 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           d_nuC_366 (coe v0) (coe v1) (coe v4) (coe v6) (coe v7)
                           (coe d_closeV_286 (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.parenC
d_parenC_406 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_CloseV_274 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parenC_406 ~v0 ~v1 v2 v3 v4 v5 v6 = du_parenC_406 v2 v3 v4 v5 v6
du_parenC_406 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  T_CloseV_274 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parenC_406 v0 v1 v2 v3 v4
  = case coe v4 of
      C_cR_278
        -> case coe v2 of
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                          (coe
                             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                             (coe
                                addInt (coe (1 :: Integer))
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (coe (\ v8 v9 -> addInt (coe (1 :: Integer)) (coe v9)))
                                   (coe (0 :: Integer)) (coe v7)))
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                   (coe (\ v8 v9 -> addInt (coe (1 :: Integer)) (coe v9)))
                                   (coe (0 :: Integer)) (coe v7)))
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                (coe MAlonzo.Code.Data.List.Base.du_length_268 v0) (coe v3)
                                (coe
                                   MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                      (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                                       coe (coe (\ v9 -> v8)))
                                      (coe (0 :: Integer)) (coe v0)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_cOther_282 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.parenK
d_parenK_428 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  () ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parenK_428 ~v0 ~v1 v2 v3 = du_parenK_428 v2 v3
du_parenK_428 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parenK_428 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_parenC_406 (coe v0) (coe v3) (coe v5) (coe v6)
                           (coe d_closeV_286 (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.arrK
d_arrK_444 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrK_444 ~v0 v1 ~v2 v3 v4 v5 = du_arrK_444 v1 v3 v4 v5
du_arrK_444 ::
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_arrK_444 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v5)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v1) (coe v8)
                                       (coe v2)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.atomA
d_atomA_470 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomA_470 v0 v1 ~v2 = du_atomA_470 v0 v1
du_atomA_470 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_atomA_470 v0 v1
  = coe
      du_atomX_478 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_extraP_200 v0 v1)
-- Once.Parser.Generic.Parser.Make.atomX
d_atomX_478 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomX_478 v0 v1 ~v2 v3 = du_atomX_478 v0 v1 v3
du_atomX_478 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_atomX_478 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.Parser.Generic.Relation.d_extraShrink_192 v0
                                    v1 v4 v6 v7)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_atomKw_482 (coe v0) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.atomKw
d_atomKw_482 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomKw_482 v0 v1 ~v2 = du_atomKw_482 v0 v1
du_atomKw_482 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_atomKw_482 v0 v1
  = coe du_atomH_486 (coe v0) (coe v1) (coe d_headV_264 (coe v1))
-- Once.Parser.Generic.Parser.Make.atomH
d_atomH_486 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_HeadV_246 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomH_486 v0 v1 v2 ~v3 = du_atomH_486 v0 v1 v2
du_atomH_486 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_HeadV_246 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_atomH_486 v0 v1 v2
  = case coe v2 of
      C_hWord_252
        -> case coe v1 of
             (:) v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Once.Parser.Token.C_TWord_8 v7
                      -> coe du_kwK_492 (coe v0) (coe v6) (coe d_kwV_182 (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_hParen_256
        -> case coe v1 of
             (:) v4 v5
               -> coe du_parenK_428 (coe v5) (coe du_typeA_556 (coe v0) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_hOther_260 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.kwK
d_kwK_492 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_KwV_124 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_kwK_492 v0 ~v1 v2 v3 ~v4 = du_kwK_492 v0 v2 v3
du_kwK_492 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_KwV_124 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_kwK_492 v0 v1 v2
  = case coe v2 of
      C_vUnit_126
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_aUnit_152 (coe v0))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (let v3 = \ v3 -> addInt (coe (1 :: Integer)) (coe v3) in
                          coe (coe (\ v4 -> v3)))
                         (coe (0 :: Integer)) (coe v1)))))
      C_vVoid_128
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_aVoid_154 (coe v0))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (let v3 = \ v3 -> addInt (coe (1 :: Integer)) (coe v3) in
                          coe (coe (\ v4 -> v3)))
                         (coe (0 :: Integer)) (coe v1)))))
      C_vInt_130
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_aInt_156 (coe v0))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (let v3 = \ v3 -> addInt (coe (1 :: Integer)) (coe v3) in
                          coe (coe (\ v4 -> v3)))
                         (coe (0 :: Integer)) (coe v1)))))
      C_vFloat_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_aFloat_158 (coe v0))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (let v3 = \ v3 -> addInt (coe (1 :: Integer)) (coe v3) in
                          coe (coe (\ v4 -> v3)))
                         (coe (0 :: Integer)) (coe v1)))))
      C_vEff_134
        -> coe
             du_twoK_498 (coe v0)
             (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_aEff_164 (coe v0))
             (coe v1) (coe du_atomA_470 (coe v0) (coe v1))
      C_vAct_136
        -> coe
             du_twoK_498 (coe v0)
             (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_aAct_166 (coe v0))
             (coe v1) (coe du_atomA_470 (coe v0) (coe v1))
      C_vMu_138
        -> coe
             du_under_54 (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                (coe MAlonzo.Code.Data.List.Base.du_length_268 v1))
             (coe
                du_mapRes_102
                (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_aMu_170 (coe v0))
                (coe du_fSumA_612 (coe v0) (coe v1)))
      C_vNu_140
        -> coe
             du_nuTry_502 (coe v0) (coe v1) (coe du_fSumA_612 (coe v0) (coe v1))
      C_vNone_144 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.twoK
d_twoK_498 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_twoK_498 v0 v1 ~v2 v3 v4 ~v5 = du_twoK_498 v0 v1 v3 v4
du_twoK_498 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_twoK_498 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           du_under_54
                           (coe
                              MAlonzo.Code.Data.List.Base.du_foldr_216
                              (let v9 = \ v9 -> addInt (coe (1 :: Integer)) (coe v9) in
                               coe (coe (\ v10 -> v9)))
                              (coe (0 :: Integer)) (coe v7))
                           (coe
                              MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                              (coe MAlonzo.Code.Data.List.Base.du_length_268 v2) (coe v8)
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                    (let v9 = \ v9 -> addInt (coe (1 :: Integer)) (coe v9) in
                                     coe (coe (\ v10 -> v9)))
                                    (coe (0 :: Integer)) (coe v2))))
                           (coe
                              du_mapRes_102 (coe v1 v5) (coe du_atomA_470 (coe v0) (coe v7)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.nuTry
d_nuTry_502 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuTry_502 v0 v1 ~v2 v3 = du_nuTry_502 v0 v1 v3
du_nuTry_502 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_nuTry_502 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_aNu_172 v0 v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                    (coe MAlonzo.Code.Data.List.Base.du_length_268 v1) (coe v7)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (let v8 = \ v8 -> addInt (coe (1 :: Integer)) (coe v8) in
                                           coe (coe (\ v9 -> v8)))
                                          (coe (0 :: Integer)) (coe v1))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe du_nuAct_508 (coe v0) (coe d_actHead'63'_240 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.nuAct
d_nuAct_508 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_nuAct_508 v0 ~v1 ~v2 v3 = du_nuAct_508 v0 v3
du_nuAct_508 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_nuAct_508 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    d_nuClose_386 (coe v0) (coe v3)
                    (coe du_fSumA_612 (coe v0) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.prodA
d_prodA_512 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodA_512 v0 v1 ~v2 = du_prodA_512 v0 v1
du_prodA_512 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_prodA_512 v0 v1
  = coe du_prodK_516 (coe v0) (coe du_atomA_470 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.prodK
d_prodK_516 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodK_516 v0 ~v1 v2 ~v3 = du_prodK_516 v0 v2
du_prodK_516 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_prodK_516 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_after'60'_72 (coe v6)
                           (coe du_prodTailA_520 (coe v0) (coe v3) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.prodTailA
d_prodTailA_520 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailA_520 v0 v1 v2 ~v3 = du_prodTailA_520 v0 v1 v2
du_prodTailA_520 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_prodTailA_520 v0 v1 v2
  = coe
      du_ptGo_526 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v2))
      (\ v3 ->
         coe
           MAlonzo.Code.Once.Parser.Generic.Relation.du_isStar'45''60'_252
           (coe v2))
-- Once.Parser.Generic.Parser.Make.ptGo
d_ptGo_526 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ptGo_526 v0 v1 v2 v3 v4 ~v5 = du_ptGo_526 v0 v1 v2 v3 v4
du_ptGo_526 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ptGo_526 v0 v1 v2 v3 v4
  = if coe v3
      then coe
             du_ptK_530 (coe v0) (coe v1) (coe v2) (coe v4 erased)
             (coe
                du_atomA_470 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
      else coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe MAlonzo.Code.Data.List.Base.du_length_268 v2))))
-- Once.Parser.Generic.Parser.Make.ptK
d_ptK_530 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ptK_530 v0 v1 v2 v3 v4 ~v5 = du_ptK_530 v0 v1 v2 v3 v4
du_ptK_530 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ptK_530 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           du_weaken_88
                           (coe
                              du_after'60'_72
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_length_268
                                    (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
                                 (coe v9) (coe v3))
                              (coe
                                 du_prodTailA_520 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Parser.Generic.Relation.d_aProd_160 v0 v1 v6)
                                 (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.sumA
d_sumA_534 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumA_534 v0 v1 ~v2 = du_sumA_534 v0 v1
du_sumA_534 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sumA_534 v0 v1
  = coe du_sumK_538 (coe v0) (coe du_prodA_512 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.sumK
d_sumK_538 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumK_538 v0 ~v1 v2 ~v3 = du_sumK_538 v0 v2
du_sumK_538 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sumK_538 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_after'60'_72 (coe v6)
                           (coe du_sumTailA_542 (coe v0) (coe v3) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.sumTailA
d_sumTailA_542 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailA_542 v0 v1 v2 ~v3 = du_sumTailA_542 v0 v1 v2
du_sumTailA_542 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sumTailA_542 v0 v1 v2
  = coe
      du_stGo_548 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v2))
      (\ v3 ->
         coe
           MAlonzo.Code.Once.Parser.Generic.Relation.du_isPlus'45''60'_260
           (coe v2))
-- Once.Parser.Generic.Parser.Make.stGo
d_stGo_548 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stGo_548 v0 v1 v2 v3 v4 ~v5 = du_stGo_548 v0 v1 v2 v3 v4
du_stGo_548 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stGo_548 v0 v1 v2 v3 v4
  = if coe v3
      then coe
             du_stK_552 (coe v0) (coe v1) (coe v2) (coe v4 erased)
             (coe
                du_prodA_512 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
      else coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe MAlonzo.Code.Data.List.Base.du_length_268 v2))))
-- Once.Parser.Generic.Parser.Make.stK
d_stK_552 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_stK_552 v0 v1 v2 v3 v4 ~v5 = du_stK_552 v0 v1 v2 v3 v4
du_stK_552 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_stK_552 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           du_weaken_88
                           (coe
                              du_after'60'_72
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_length_268
                                    (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
                                 (coe v9) (coe v3))
                              (coe
                                 du_sumTailA_542 (coe v0)
                                 (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_aSum_162 v0 v1 v6)
                                 (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.typeA
d_typeA_556 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeA_556 v0 v1 ~v2 = du_typeA_556 v0 v1
du_typeA_556 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_typeA_556 v0 v1
  = coe du_typeK_560 (coe v0) (coe du_sumA_534 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.typeK
d_typeK_560 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeK_560 v0 ~v1 v2 ~v3 = du_typeK_560 v0 v2
du_typeK_560 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_typeK_560 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_after'60'_72 (coe v6)
                           (coe du_arrowTailA_564 (coe v0) (coe v3) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.arrowTailA
d_arrowTailA_564 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailA_564 v0 v1 v2 ~v3 = du_arrowTailA_564 v0 v1 v2
du_arrowTailA_564 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_arrowTailA_564 v0 v1 v2
  = coe
      du_atGo_572 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Relation.d_arrowDir_22 (coe v2))
      (\ v3 ->
         coe
           MAlonzo.Code.Once.Parser.Generic.Relation.du_arrowDir'45'A'45''60'_268
           (coe v2))
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Once.Parser.Generic.Relation.du_arrowDir'45'G'45''60'_278
           (coe v2))
-- Once.Parser.Generic.Parser.Make.atGo
d_atGo_572 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atGo_572 v0 v1 v2 v3 v4 v5 ~v6 = du_atGo_572 v0 v1 v2 v3 v4 v5
du_atGo_572 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Once.Parser.Generic.Relation.T_ArrowDir_12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  (MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_atGo_572 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.Parser.Generic.Relation.C_adG_14 v6
        -> coe
             du_arrK_444
             (coe
                MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_168 v0 v6 v1)
             (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34 (coe v2))
             (coe v5 v6 erased)
             (coe
                du_typeA_556 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop2_34 (coe v2)))
      MAlonzo.Code.Once.Parser.Generic.Relation.C_adA_16
        -> coe
             du_arrK_444
             (coe
                MAlonzo.Code.Once.Parser.Generic.Relation.d_aArrow_168 v0
                (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) v1)
             (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2))
             (coe v4 erased)
             (coe
                du_typeA_556 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
      MAlonzo.Code.Once.Parser.Generic.Relation.C_adR_18
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.Parser.Generic.Relation.C_adD_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe MAlonzo.Code.Data.List.Base.du_length_268 v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.fAtomA
d_fAtomA_576 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomA_576 v0 v1 ~v2 = du_fAtomA_576 v0 v1
du_fAtomA_576 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fAtomA_576 v0 v1
  = coe du_fAtomH_580 (coe v0) (coe v1) (coe d_headV_264 (coe v1))
-- Once.Parser.Generic.Parser.Make.fAtomH
d_fAtomH_580 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_HeadV_246 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomH_580 v0 v1 v2 ~v3 = du_fAtomH_580 v0 v1 v2
du_fAtomH_580 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_HeadV_246 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fAtomH_580 v0 v1 v2
  = case coe v2 of
      C_hWord_252
        -> case coe v1 of
             (:) v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Once.Parser.Token.C_TWord_8 v7
                      -> coe du_fkwK_586 (coe v0) (coe v6) (coe d_fkwV_218 (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_hParen_256
        -> case coe v1 of
             (:) v4 v5
               -> coe du_parenK_428 (coe v5) (coe du_fSumA_612 (coe v0) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_hOther_260 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.fkwK
d_fkwK_586 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_FKwV_186 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fkwK_586 v0 ~v1 v2 v3 ~v4 = du_fkwK_586 v0 v2 v3
du_fkwK_586 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  T_FKwV_186 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fkwK_586 v0 v1 v2
  = case coe v2 of
      C_fvId_188
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_fId_178 (coe v0))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (let v3 = \ v3 -> addInt (coe (1 :: Integer)) (coe v3) in
                          coe (coe (\ v4 -> v3)))
                         (coe (0 :: Integer)) (coe v1)))))
      C_fvK_190
        -> coe
             du_under_54 (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)
             (coe
                MAlonzo.Code.Data.Nat.Properties.d_n'60'1'43'n_3220
                (coe MAlonzo.Code.Data.List.Base.du_length_268 v1))
             (coe
                du_mapRes_102
                (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_fK_176 (coe v0))
                (coe du_atomA_470 (coe v0) (coe v1)))
      C_fvNone_194 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.fProdA
d_fProdA_590 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdA_590 v0 v1 ~v2 = du_fProdA_590 v0 v1
du_fProdA_590 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fProdA_590 v0 v1
  = coe du_fProdK_594 (coe v0) (coe du_fAtomA_576 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.fProdK
d_fProdK_594 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdK_594 v0 ~v1 v2 ~v3 = du_fProdK_594 v0 v2
du_fProdK_594 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fProdK_594 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_after'60'_72 (coe v6)
                           (coe du_fProdTailA_598 (coe v0) (coe v3) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.fProdTailA
d_fProdTailA_598 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailA_598 v0 v1 v2 ~v3 = du_fProdTailA_598 v0 v1 v2
du_fProdTailA_598 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fProdTailA_598 v0 v1 v2
  = coe
      du_fptGo_604 (coe v0) (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_isStar_8 (coe v2))
      (\ v3 ->
         coe
           MAlonzo.Code.Once.Parser.Generic.Relation.du_isStar'45''60'_252
           (coe v2))
-- Once.Parser.Generic.Parser.Make.fptGo
d_fptGo_604 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fptGo_604 v0 v1 v2 v3 v4 ~v5 = du_fptGo_604 v0 v1 v2 v3 v4
du_fptGo_604 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fptGo_604 v0 v1 v2 v3 v4
  = if coe v3
      then coe
             du_fptK_608 (coe v0) (coe v1) (coe v2) (coe v4 erased)
             (coe
                du_fAtomA_576 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
      else coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe MAlonzo.Code.Data.List.Base.du_length_268 v2))))
-- Once.Parser.Generic.Parser.Make.fptK
d_fptK_608 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fptK_608 v0 v1 v2 v3 v4 ~v5 = du_fptK_608 v0 v1 v2 v3 v4
du_fptK_608 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fptK_608 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           du_weaken_88
                           (coe
                              du_after'60'_72
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_length_268
                                    (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
                                 (coe v9) (coe v3))
                              (coe
                                 du_fProdTailA_598 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Parser.Generic.Relation.d_fProd_182 v0 v1 v6)
                                 (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.fSumA
d_fSumA_612 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumA_612 v0 v1 ~v2 = du_fSumA_612 v0 v1
du_fSumA_612 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fSumA_612 v0 v1
  = coe du_fSumK_616 (coe v0) (coe du_fProdA_590 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.fSumK
d_fSumK_616 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumK_616 v0 ~v1 v2 ~v3 = du_fSumK_616 v0 v2
du_fSumK_616 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fSumK_616 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           du_after'60'_72 (coe v6)
                           (coe du_fSumTailA_620 (coe v0) (coe v3) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.fSumTailA
d_fSumTailA_620 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailA_620 v0 v1 v2 ~v3 = du_fSumTailA_620 v0 v1 v2
du_fSumTailA_620 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fSumTailA_620 v0 v1 v2
  = coe
      du_fstGo_626 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Once.Parser.Generic.Relation.d_isPlus_10 (coe v2))
      (\ v3 ->
         coe
           MAlonzo.Code.Once.Parser.Generic.Relation.du_isPlus'45''60'_260
           (coe v2))
-- Once.Parser.Generic.Parser.Make.fstGo
d_fstGo_626 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fstGo_626 v0 v1 v2 v3 v4 ~v5 = du_fstGo_626 v0 v1 v2 v3 v4
du_fstGo_626 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Bool ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fstGo_626 v0 v1 v2 v3 v4
  = if coe v3
      then coe
             du_fstK_630 (coe v0) (coe v1) (coe v2) (coe v4 erased)
             (coe
                du_fProdA_590 (coe v0)
                (coe
                   MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
      else coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe MAlonzo.Code.Data.List.Base.du_length_268 v2))))
-- Once.Parser.Generic.Parser.Make.fstK
d_fstK_630 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fstK_630 v0 v1 v2 v3 v4 ~v5 = du_fstK_630 v0 v1 v2 v3 v4
du_fstK_630 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fstK_630 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> coe
                           du_weaken_88
                           (coe
                              du_after'60'_72
                              (coe
                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du_length_268
                                    (MAlonzo.Code.Once.Parser.Generic.Relation.d_drop1_24 (coe v2)))
                                 (coe v9) (coe v3))
                              (coe
                                 du_fSumTailA_620 (coe v0)
                                 (coe MAlonzo.Code.Once.Parser.Generic.Relation.d_fSum_180 v0 v1 v6)
                                 (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Generic.Parser.Make.atomP
d_atomP_1096 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_atomP_1096 v0 v1
  = coe du_forget'60'_32 (coe du_atomA_470 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.prodP
d_prodP_1098 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodP_1098 v0 v1
  = coe du_forget'60'_32 (coe du_prodA_512 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.sumP
d_sumP_1100 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumP_1100 v0 v1
  = coe du_forget'60'_32 (coe du_sumA_534 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.typeP
d_typeP_1102 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeP_1102 v0 v1
  = coe du_forget'60'_32 (coe du_typeA_556 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.prodTailP
d_prodTailP_1112 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_prodTailP_1112 v0 v1 v2
  = coe
      du_forget'8804'_42
      (coe du_prodTailA_520 (coe v0) (coe v1) (coe v2))
-- Once.Parser.Generic.Parser.Make.sumTailP
d_sumTailP_1114 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sumTailP_1114 v0 v1 v2
  = coe
      du_forget'8804'_42 (coe du_sumTailA_542 (coe v0) (coe v1) (coe v2))
-- Once.Parser.Generic.Parser.Make.arrowTailP
d_arrowTailP_1116 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_arrowTailP_1116 v0 v1 v2
  = coe
      du_forget'8804'_42
      (coe du_arrowTailA_564 (coe v0) (coe v1) (coe v2))
-- Once.Parser.Generic.Parser.Make.fAtomP
d_fAtomP_1130 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fAtomP_1130 v0 v1
  = coe du_forget'60'_32 (coe du_fAtomA_576 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.fProdP
d_fProdP_1132 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdP_1132 v0 v1
  = coe du_forget'60'_32 (coe du_fProdA_590 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.fSumP
d_fSumP_1134 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumP_1134 v0 v1
  = coe du_forget'60'_32 (coe du_fSumA_612 (coe v0) (coe v1))
-- Once.Parser.Generic.Parser.Make.fProdTailP
d_fProdTailP_1142 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fProdTailP_1142 v0 v1 v2
  = coe
      du_forget'8804'_42
      (coe du_fProdTailA_598 (coe v0) (coe v1) (coe v2))
-- Once.Parser.Generic.Parser.Make.fSumTailP
d_fSumTailP_1144 ::
  MAlonzo.Code.Once.Parser.Generic.Relation.T_TyAlg_46 ->
  AgdaAny ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fSumTailP_1144 v0 v1 v2
  = coe
      du_forget'8804'_42
      (coe du_fSumTailA_620 (coe v0) (coe v1) (coe v2))
