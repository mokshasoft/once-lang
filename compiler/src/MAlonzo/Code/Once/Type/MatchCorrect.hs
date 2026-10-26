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

module MAlonzo.Code.Once.Type.MatchCorrect where

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
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Match
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Type.MatchCorrect.lookup-head
d_lookup'45'head_14 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'head_14 = erased
-- Once.Type.MatchCorrect.Consistent
d_Consistent_42 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_Consistent_42 = erased
-- Once.Type.MatchCorrect.consistent-[]
d_consistent'45''91''93'_56 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_consistent'45''91''93'_56 = erased
-- Once.Type.MatchCorrect.consistent-∷
d_consistent'45''8759'_72 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_consistent'45''8759'_72 = erased
-- Once.Type.MatchCorrect.Matches
d_Matches_140 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_Matches_140 = erased
-- Once.Type.MatchCorrect.extend-ok
d_extend'45'ok_158 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extend'45'ok_158 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.Type.Match.du_lookupSubst_12 (coe v3) (coe v2) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
           -> let v7
                    = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                        (coe v0) (coe v1 v3) (coe v6) in
              coe
                (case coe v7 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                     -> if coe v8
                          then coe
                                 seq (coe v9)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4)))
                          else coe
                                 seq (coe v9) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v1 v3))
                   (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.MatchCorrect.bind-ok
d_bind'45'ok_228 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   Maybe [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bind'45'ok_228 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_bind'45'ok_228 v4 v5
du_bind'45'ok_228 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
   (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
    MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
    MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bind'45'ok_228 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5 -> coe v1 v2 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.MatchCorrect.inst-ok
d_inst'45'ok_248 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst'45'ok_248 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28 v5 v6
        -> coe
             du_bind'45'ok_228
             (coe d_inst'45'ok_248 (coe v0) (coe v1) (coe v5) (coe v3) erased)
             (coe d_inst'45'ok_248 (coe v0) (coe v1) (coe v6))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v5 v6
        -> coe
             du_bind'45'ok_228
             (coe d_inst'45'ok_248 (coe v0) (coe v1) (coe v5) (coe v3) erased)
             (coe d_inst'45'ok_248 (coe v0) (coe v1) (coe v6))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v5 v6 v7
        -> let v8
                 = MAlonzo.Code.Once.Type.DecEq.d__'8799'q__6 (coe v6) (coe v6) in
           coe
             (case coe v8 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                  -> if coe v9
                       then coe
                              seq (coe v10)
                              (coe
                                 du_bind'45'ok_228
                                 (coe d_inst'45'ok_248 (coe v0) (coe v1) (coe v5) (coe v3) erased)
                                 (coe d_inst'45'ok_248 (coe v0) (coe v1) (coe v7)))
                       else coe
                              seq (coe v10) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v5 v6
        -> coe
             du_bind'45'ok_228
             (coe d_inst'45'ok_248 (coe v0) (coe v1) (coe v5) (coe v3) erased)
             (coe d_inst'45'ok_248 (coe v0) (coe v1) (coe v6))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v5 v6
        -> coe
             du_bind'45'ok_228
             (coe d_inst'45'ok_248 (coe v0) (coe v1) (coe v5) (coe v3) erased)
             (coe d_inst'45'ok_248 (coe v0) (coe v1) (coe v6))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v5
        -> coe d_instF'45'ok_258 (coe v0) (coe v1) (coe v5) (coe v3) erased
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v5 v6
        -> coe
             seq (coe v6)
             (coe d_instF'45'ok_258 (coe v0) (coe v1) (coe v5) (coe v3) erased)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42 v5
        -> coe
             d_extend'45'ok_158 (coe v0) (coe v1) (coe v3) (coe v5) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.MatchCorrect.instF-ok
d_instF'45'ok_258 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8) ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instF'45'ok_258 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v5
        -> coe d_inst'45'ok_248 (coe v0) (coe v1) (coe v5) (coe v3) erased
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v5 v6
        -> coe
             du_bind'45'ok_228
             (coe d_instF'45'ok_258 (coe v0) (coe v1) (coe v5) (coe v3) erased)
             (coe d_instF'45'ok_258 (coe v0) (coe v1) (coe v6))
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v5 v6
        -> coe
             du_bind'45'ok_228
             (coe d_instF'45'ok_258 (coe v0) (coe v1) (coe v5) (coe v3) erased)
             (coe d_instF'45'ok_258 (coe v0) (coe v1) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.MatchCorrect.instantiate-complete
d_instantiate'45'complete_468 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instantiate'45'complete_468 v0 v1 ~v2 v3
  = du_instantiate'45'complete_468 v0 v1 v3
du_instantiate'45'complete_468 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_instantiate'45'complete_468 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> let v5
                 = d_inst'45'ok_248
                     (coe v0) (coe v3) (coe v1)
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased in
           coe
             (case coe v5 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v8)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.MatchCorrect.Extends
d_Extends_492 a0 a1 a2 = ()
data T_Extends_492 = C_mkExt_512
-- Once.Type.MatchCorrect.Extends.ext
d_ext_510 ::
  T_Extends_492 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext_510 = erased
-- Once.Type.MatchCorrect.θof-aux
d_θof'45'aux_516 ::
  Integer ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_θof'45'aux_516 ~v0 v1 = du_θof'45'aux_516 v1
du_θof'45'aux_516 ::
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_θof'45'aux_516 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.MatchCorrect.θof
d_θof_522 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_θof_522 ~v0 v1 v2 = du_θof_522 v1 v2
du_θof_522 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_θof_522 v0 v1
  = coe
      du_θof'45'aux_516
      (coe
         MAlonzo.Code.Once.Type.Match.du_lookupSubst_12 (coe v1) (coe v0))
-- Once.Type.MatchCorrect.θof-just
d_θof'45'just_536 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_θof'45'just_536 = erased
-- Once.Type.MatchCorrect.nothing≢just
d_nothing'8802'just_548 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nothing'8802'just_548 = erased
-- Once.Type.MatchCorrect.var-sound
d_var'45'sound_562 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_var'45'sound_562 v0 v1 v2 v3 ~v4 ~v5
  = du_var'45'sound_562 v0 v1 v2 v3
du_var'45'sound_562 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_var'45'sound_562 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.Type.Match.du_lookupSubst_12 (coe v1) (coe v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> let v6
                    = MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228
                        (coe v0) (coe v2) (coe v5) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                     -> coe
                          seq (coe v7)
                          (coe
                             seq (coe v8)
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Type.MatchCorrect._.ext′
d_ext'8242'_678 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext'8242'_678 = erased
-- Once.Type.MatchCorrect.bin-sound
d_bin'45'sound_744 ::
  Integer ->
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
d_bin'45'sound_744 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                   ~v12 v13 v14 v15
  = du_bin'45'sound_744 v10 v11 v13 v14 v15
du_bin'45'sound_744 ::
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
du_bin'45'sound_744 v0 v1 v2 v3 v4
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
-- Once.Type.MatchCorrect.map-sound
d_map'45'sound_830 ::
  Integer ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  ([MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny) ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_map'45'sound_830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_map'45'sound_830 v8
du_map'45'sound_830 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_map'45'sound_830 v0 = coe v0
-- Once.Type.MatchCorrect.inst-sound
d_inst'45'sound_854 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst'45'sound_854 v0 v1 v2 v3 v4 ~v5
  = du_inst'45'sound_854 v0 v1 v2 v3 v4
du_inst'45'sound_854 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inst'45'sound_854 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PUnit_20
        -> coe
             seq (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PVoid_22
        -> coe
             seq (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PInt_24
        -> coe
             seq (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PFloat_26
        -> coe
             seq (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'42'__28 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v7 v8
               -> coe
                    du_bin'45'sound_744 (coe v4)
                    (coe
                       MAlonzo.Code.Once.Type.Match.d_instantiateAcc_104 (coe v0) (coe v5)
                       (coe v7) (coe v3))
                    (\ v9 v10 ->
                       coe du_inst'45'sound_854 (coe v0) (coe v5) (coe v7) (coe v3) v9)
                    (\ v9 v10 v11 ->
                       coe du_inst'45'sound_854 (coe v0) (coe v6) (coe v8) v9 v10)
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'43'__30 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v7 v8
               -> coe
                    du_bin'45'sound_744 (coe v4)
                    (coe
                       MAlonzo.Code.Once.Type.Match.d_instantiateAcc_104 (coe v0) (coe v5)
                       (coe v7) (coe v3))
                    (\ v9 v10 ->
                       coe du_inst'45'sound_854 (coe v0) (coe v5) (coe v7) (coe v3) v9)
                    (\ v9 v10 v11 ->
                       coe du_inst'45'sound_854 (coe v0) (coe v6) (coe v8) v9 v10)
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8658''91'_'93'__32 v5 v6 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v8 v9 v10
               -> case coe v9 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v11 v12
                      -> case coe v12 of
                           MAlonzo.Code.Once.Spec.Grade.C_fin_42 v13
                             -> coe
                                  seq (coe v13)
                                  (let v14
                                         = MAlonzo.Code.Once.Type.DecEq.d__'8799'q__6
                                             (coe v6) (coe v11) in
                                   coe
                                     (case coe v14 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                          -> coe
                                               seq (coe v15)
                                               (coe
                                                  seq (coe v16)
                                                  (coe
                                                     du_bin'45'sound_744 (coe v4)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.Match.d_instantiateAcc_104
                                                        (coe v0) (coe v5) (coe v8) (coe v3))
                                                     (\ v17 v18 ->
                                                        coe
                                                          du_inst'45'sound_854 (coe v0) (coe v5)
                                                          (coe v8) (coe v3) v17)
                                                     (\ v17 v18 v19 ->
                                                        coe
                                                          du_inst'45'sound_854 (coe v0) (coe v7)
                                                          (coe v10) v17 v18)
                                                     erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PAct_34 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v10 v11
                      -> coe
                           seq (coe v10)
                           (case coe v11 of
                              MAlonzo.Code.Once.Spec.Grade.C_fin_42 v12
                                -> coe
                                     seq (coe v12)
                                     (coe
                                        du_bin'45'sound_744 (coe v4)
                                        (coe
                                           MAlonzo.Code.Once.Type.Match.d_instantiateAcc_104
                                           (coe v0) (coe v5) (coe v7) (coe v3))
                                        (\ v13 v14 ->
                                           coe
                                             du_inst'45'sound_854 (coe v0) (coe v5) (coe v7)
                                             (coe v3) v13)
                                        (\ v13 v14 v15 ->
                                           coe
                                             du_inst'45'sound_854 (coe v0) (coe v6) (coe v9) v13
                                             v14)
                                        erased)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PEff_36 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v7 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v10 v11
                      -> coe
                           seq (coe v10)
                           (coe
                              seq (coe v11)
                              (coe
                                 du_bin'45'sound_744 (coe v4)
                                 (coe
                                    MAlonzo.Code.Once.Type.Match.d_instantiateAcc_104 (coe v0)
                                    (coe v5) (coe v7) (coe v3))
                                 (\ v12 v13 ->
                                    coe
                                      du_inst'45'sound_854 (coe v0) (coe v5) (coe v7) (coe v3) v12)
                                 (\ v12 v13 v14 ->
                                    coe du_inst'45'sound_854 (coe v0) (coe v6) (coe v9) v12 v13)
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pμ_38 v5
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_μ_28 v6
               -> coe
                    du_instF'45'sound_868 (coe v0) (coe v5) (coe v6) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_Pν_40 v5 v6
        -> coe
             seq (coe v6)
             (case coe v2 of
                MAlonzo.Code.Once.Spec.Type.C_ν_30 v7 v8
                  -> coe
                       seq (coe v8)
                       (coe
                          du_instF'45'sound_868 (coe v0) (coe v5) (coe v7) (coe v3) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PTVar_42 v5
        -> coe du_var'45'sound_562 (coe v0) (coe v5) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.MatchCorrect.instF-sound
d_instF'45'sound_868 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instF'45'sound_868 v0 v1 v2 v3 v4 ~v5
  = du_instF'45'sound_868 v0 v1 v2 v3 v4
du_instF'45'sound_868 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyFunctor_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_instF'45'sound_868 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PK_12 v5
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C_K_38 v6
               -> coe
                    du_inst'45'sound_854 (coe v0) (coe v5) (coe v6) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_PId_14
        -> coe
             seq (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8853'__16 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v7 v8
               -> coe
                    du_bin'45'sound_744 (coe v4)
                    (coe
                       MAlonzo.Code.Once.Type.Match.d_instantiateFunctor_108 (coe v0)
                       (coe v5) (coe v7) (coe v3))
                    (\ v9 v10 ->
                       coe du_instF'45'sound_868 (coe v0) (coe v5) (coe v7) (coe v3) v9)
                    (\ v9 v10 v11 ->
                       coe du_instF'45'sound_868 (coe v0) (coe v6) (coe v8) v9 v10)
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C__P'8855'__18 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v7 v8
               -> coe
                    du_bin'45'sound_744 (coe v4)
                    (coe
                       MAlonzo.Code.Once.Type.Match.d_instantiateFunctor_108 (coe v0)
                       (coe v5) (coe v7) (coe v3))
                    (\ v9 v10 ->
                       coe du_instF'45'sound_868 (coe v0) (coe v5) (coe v7) (coe v3) v9)
                    (\ v9 v10 v11 ->
                       coe du_instF'45'sound_868 (coe v0) (coe v6) (coe v8) v9 v10)
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Type.MatchCorrect.instantiate-sound
d_instantiate'45'sound_1850 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instantiate'45'sound_1850 v0 v1 v2 v3 ~v4
  = du_instantiate'45'sound_1850 v0 v1 v2 v3
du_instantiate'45'sound_1850 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_instantiate'45'sound_1850 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_θof_522 (coe v3))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            du_inst'45'sound_854 (coe v0) (coe v1) (coe v2)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3))
         v3 erased)
