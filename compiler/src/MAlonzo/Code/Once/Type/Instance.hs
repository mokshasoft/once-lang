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

module MAlonzo.Code.Once.Type.Instance where

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
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.DecEq
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Type.Match
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Type.Instance.lookup-head
d_lookup'45'head_12 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'head_12 = erased
-- Once.Type.Instance.Consistent
d_Consistent_38 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_Consistent_38 = erased
-- Once.Type.Instance.consistent-[]
d_consistent'45''91''93'_50 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_consistent'45''91''93'_50 = erased
-- Once.Type.Instance.consistent-∷
d_consistent'45''8759'_64 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_consistent'45''8759'_64 = erased
-- Once.Type.Instance.Matches
d_Matches_130 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_Matches_130 = erased
-- Once.Type.Instance.extend-ok
d_extend'45'ok_144 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extend'45'ok_144 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.Type.Match.d_lookupSubst_8 (coe v2) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> let v6
                    = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__214
                        (coe v0 v2) (coe v5) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                     -> if coe v7
                          then coe
                                 seq (coe v8)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v3)))
                          else coe
                                 seq (coe v8) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v0 v2))
                   (coe v1))
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.Instance.bind-ok
d_bind'45'ok_212 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bind'45'ok_212 ~v0 ~v1 ~v2 v3 v4 = du_bind'45'ok_212 v3 v4
du_bind'45'ok_212 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bind'45'ok_212 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5 -> coe v1 v2 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.inst-ok
d_inst'45'ok_230 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst'45'ok_230 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v3))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PVoid_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v3))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v4 v5
        -> coe
             du_bind'45'ok_212
             (coe d_inst'45'ok_230 (coe v0) (coe v4) (coe v2) erased)
             (coe d_inst'45'ok_230 (coe v0) (coe v5))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v4 v5
        -> coe
             du_bind'45'ok_212
             (coe d_inst'45'ok_230 (coe v0) (coe v4) (coe v2) erased)
             (coe d_inst'45'ok_230 (coe v0) (coe v5))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v4 v5 v6
        -> let v7
                 = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'q__8
                     (coe v5) (coe v5) in
           coe
             (case coe v7 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                  -> if coe v8
                       then coe
                              seq (coe v9)
                              (coe
                                 du_bind'45'ok_212
                                 (coe d_inst'45'ok_230 (coe v0) (coe v4) (coe v2) erased)
                                 (coe d_inst'45'ok_230 (coe v0) (coe v6)))
                       else coe
                              seq (coe v9) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v4 v5
        -> coe
             du_bind'45'ok_212
             (coe d_inst'45'ok_230 (coe v0) (coe v4) (coe v2) erased)
             (coe d_inst'45'ok_230 (coe v0) (coe v5))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v4 v5
        -> coe
             du_bind'45'ok_212
             (coe d_inst'45'ok_230 (coe v0) (coe v4) (coe v2) erased)
             (coe d_inst'45'ok_230 (coe v0) (coe v5))
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v4
        -> coe d_instF'45'ok_238 (coe v0) (coe v4) (coe v2) erased
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v4 v5
        -> coe
             seq (coe v5)
             (coe d_instF'45'ok_238 (coe v0) (coe v4) (coe v2) erased)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v3))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PFloat_40
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v3))
      MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v4
        -> coe d_extend'45'ok_144 (coe v0) (coe v2) (coe v4) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.instF-ok
d_instF'45'ok_238 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instF'45'ok_238 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v4
        -> coe d_inst'45'ok_230 (coe v0) (coe v4) (coe v2) erased
      MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v3))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v4 v5
        -> coe
             du_bind'45'ok_212
             (coe d_instF'45'ok_238 (coe v0) (coe v4) (coe v2) erased)
             (coe d_instF'45'ok_238 (coe v0) (coe v5))
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v4 v5
        -> coe
             du_bind'45'ok_212
             (coe d_instF'45'ok_238 (coe v0) (coe v4) (coe v2) erased)
             (coe d_instF'45'ok_238 (coe v0) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.instantiate-complete
d_instantiate'45'complete_462 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instantiate'45'complete_462 v0 ~v1 v2
  = du_instantiate'45'complete_462 v0 v2
du_instantiate'45'complete_462 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_instantiate'45'complete_462 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> let v4
                 = d_inst'45'ok_230
                     (coe v2) (coe v0)
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v7)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.Extends
d_Extends_484 a0 a1 = ()
data T_Extends_484 = C_mkExt_502
-- Once.Type.Instance.Extends.ext
d_ext_500 ::
  T_Extends_484 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext_500 = erased
-- Once.Type.Instance.θof-aux
d_θof'45'aux_504 ::
  Maybe MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_θof'45'aux_504 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Lang.Type.C_Unit_20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.θof
d_θof_508 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8
d_θof_508 v0 v1
  = coe
      d_θof'45'aux_504
      (coe
         MAlonzo.Code.Once.Type.Match.d_lookupSubst_8 (coe v1) (coe v0))
-- Once.Type.Instance.θof-just
d_θof'45'just_520 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_θof'45'just_520 = erased
-- Once.Type.Instance.nothing≢just
d_nothing'8802'just_530 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_530 = erased
-- Once.Type.Instance.var-sound
d_var'45'sound_542 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_var'45'sound_542 v0 v1 v2 ~v3 ~v4 = du_var'45'sound_542 v0 v1 v2
du_var'45'sound_542 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_var'45'sound_542 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Type.Match.d_lookupSubst_8 (coe v0) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> let v5
                    = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'T__214
                        (coe v1) (coe v4) in
              coe
                (case coe v5 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                     -> coe
                          seq (coe v6)
                          (coe
                             seq (coe v7)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.Instance._.ext′
d_ext'8242'_658 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'8242'_658 = erased
-- Once.Type.Instance.bin-sound
d_bin'45'sound_722 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny) ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bin'45'sound_722 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11
                   v12 v13 v14
  = du_bin'45'sound_722 v9 v10 v12 v13 v14
du_bin'45'sound_722 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bin'45'sound_722 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> let v6 = coe v2 v5 erased in
           coe
             (let v7 = coe v3 v5 v0 v4 in
              coe
                (coe
                   seq (coe v6)
                   (coe
                      seq (coe v7)
                      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.map-sound
d_map'45'sound_806 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny) ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_map'45'sound_806 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_map'45'sound_806 v7
du_map'45'sound_806 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_map'45'sound_806 v0 = coe v0
-- Once.Type.Instance.inst-sound
d_inst'45'sound_828 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst'45'sound_828 v0 v1 v2 v3 ~v4
  = du_inst'45'sound_828 v0 v1 v2 v3
du_inst'45'sound_828 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inst'45'sound_828 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PUnit_20
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PVoid_22
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'42'__24 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v6 v7
               -> coe
                    du_bin'45'sound_722 (coe v3)
                    (coe
                       MAlonzo.Code.Once.Type.Match.d_instantiateAcc_92 (coe v4) (coe v6)
                       (coe v2))
                    (\ v8 v9 -> coe du_inst'45'sound_828 (coe v4) (coe v6) (coe v2) v8)
                    (\ v8 v9 v10 -> coe du_inst'45'sound_828 (coe v5) (coe v7) v8 v9)
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'43'__26 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v6 v7
               -> coe
                    du_bin'45'sound_722 (coe v3)
                    (coe
                       MAlonzo.Code.Once.Type.Match.d_instantiateAcc_92 (coe v4) (coe v6)
                       (coe v2))
                    (\ v8 v9 -> coe du_inst'45'sound_828 (coe v4) (coe v6) (coe v2) v8)
                    (\ v8 v9 v10 -> coe du_inst'45'sound_828 (coe v5) (coe v7) v8 v9)
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8658''91'_'93'__28 v4 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v7 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v10 v11
                      -> coe
                           seq (coe v11)
                           (let v12
                                  = MAlonzo.Code.Once.Lang.Type.DecEq.d__'8799'q__8
                                      (coe v5) (coe v10) in
                            coe
                              (case coe v12 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                   -> coe
                                        seq (coe v13)
                                        (coe
                                           seq (coe v14)
                                           (coe
                                              du_bin'45'sound_722 (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Type.Match.d_instantiateAcc_92
                                                 (coe v4) (coe v7) (coe v2))
                                              (\ v15 v16 ->
                                                 coe
                                                   du_inst'45'sound_828 (coe v4) (coe v7) (coe v2)
                                                   v15)
                                              (\ v15 v16 v17 ->
                                                 coe du_inst'45'sound_828 (coe v6) (coe v9) v15 v16)
                                              erased))
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C_PEff_30 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v6 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v9 v10
                      -> coe
                           seq (coe v9)
                           (coe
                              seq (coe v10)
                              (coe
                                 du_bin'45'sound_722 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Type.Match.d_instantiateAcc_92 (coe v4)
                                    (coe v6) (coe v2))
                                 (\ v11 v12 ->
                                    coe du_inst'45'sound_828 (coe v4) (coe v6) (coe v2) v11)
                                 (\ v11 v12 v13 ->
                                    coe du_inst'45'sound_828 (coe v5) (coe v8) v11 v12)
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C_PAct_32 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v6 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v9 v10
                      -> coe
                           seq (coe v9)
                           (coe
                              seq (coe v10)
                              (coe
                                 du_bin'45'sound_722 (coe v3)
                                 (coe
                                    MAlonzo.Code.Once.Type.Match.d_instantiateAcc_92 (coe v4)
                                    (coe v6) (coe v2))
                                 (\ v11 v12 ->
                                    coe du_inst'45'sound_828 (coe v4) (coe v6) (coe v2) v11)
                                 (\ v11 v12 v13 ->
                                    coe du_inst'45'sound_828 (coe v5) (coe v8) v11 v12)
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pμ'45'type_34 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v5
               -> coe du_instF'45'sound_840 (coe v4) (coe v5) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C_Pν'45'type_36 v4 v5
        -> coe
             seq (coe v5)
             (case coe v1 of
                MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v6 v7
                  -> coe
                       seq (coe v7)
                       (coe du_instF'45'sound_840 (coe v4) (coe v6) (coe v2) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PInt_38
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PFloat_40
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Lang.Type.Poly.C_PTVar_42 v4
        -> coe du_var'45'sound_542 (coe v4) (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.instF-sound
d_instF'45'sound_840 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instF'45'sound_840 v0 v1 v2 v3 ~v4
  = du_instF'45'sound_840 v0 v1 v2 v3
du_instF'45'sound_840 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_instF'45'sound_840 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Poly.C_PK_12 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C_K_12 v5
               -> coe du_inst'45'sound_828 (coe v4) (coe v5) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C_PId_14
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8853'__16 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v6 v7
               -> coe
                    du_bin'45'sound_722 (coe v3)
                    (coe
                       MAlonzo.Code.Once.Type.Match.d_instantiateFunctor_94 (coe v4)
                       (coe v6) (coe v2))
                    (\ v8 v9 ->
                       coe du_instF'45'sound_840 (coe v4) (coe v6) (coe v2) v8)
                    (\ v8 v9 v10 -> coe du_instF'45'sound_840 (coe v5) (coe v7) v8 v9)
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.Poly.C__P'8855'__18 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v6 v7
               -> coe
                    du_bin'45'sound_722 (coe v3)
                    (coe
                       MAlonzo.Code.Once.Type.Match.d_instantiateFunctor_94 (coe v4)
                       (coe v6) (coe v2))
                    (\ v8 v9 ->
                       coe du_instF'45'sound_840 (coe v4) (coe v6) (coe v2) v8)
                    (\ v8 v9 v10 -> coe du_instF'45'sound_840 (coe v5) (coe v7) v8 v9)
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.Instance.instantiate-sound
d_instantiate'45'sound_2038 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instantiate'45'sound_2038 v0 v1 v2 ~v3
  = du_instantiate'45'sound_2038 v0 v1 v2
du_instantiate'45'sound_2038 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_instantiate'45'sound_2038 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_θof_508 (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            du_inst'45'sound_828 (coe v0) (coe v1)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v2))
         v2 erased)
