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

module MAlonzo.Code.Once.Adequacy.NameClash where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.NameClash.∧-elimˡ
d_'8743''45'elim'737'_10 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'elim'737'_10 = erased
-- Once.Adequacy.NameClash.∧-elimʳ
d_'8743''45'elim'691'_16 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'elim'691'_16 = erased
-- Once.Adequacy.NameClash.not-true→false
d_not'45'true'8594'false_22 ::
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'true'8594'false_22 = erased
-- Once.Adequacy.NameClash.T≢F
d_T'8802'F_24 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_T'8802'F_24 = erased
-- Once.Adequacy.NameClash.allIdentContinue-sound
d_allIdentContinue'45'sound_30 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_allIdentContinue'45'sound_30 v0 ~v1
  = du_allIdentContinue'45'sound_30 v0
du_allIdentContinue'45'sound_30 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_allIdentContinue'45'sound_30 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
             (coe du_allIdentContinue'45'sound_30 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.NameClash.validCharsB-sound
d_validCharsB'45'sound_40 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_validCharsB'45'sound_40 v0 ~v1 = du_validCharsB'45'sound_40 v0
du_validCharsB'45'sound_40 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> AgdaAny
du_validCharsB'45'sound_40 v0
  = case coe v0 of
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
             (coe du_allIdentContinue'45'sound_30 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.NameClash.validIdentB-sound
d_validIdentB'45'sound_50 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_validIdentB'45'sound_50 v0 ~v1 = du_validIdentB'45'sound_50 v0
du_validIdentB'45'sound_50 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
du_validIdentB'45'sound_50 v0
  = coe
      du_validCharsB'45'sound_40
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Once.Adequacy.NameClash.allValidIdentB-sound
d_allValidIdentB'45'sound_58 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_allValidIdentB'45'sound_58 v0 ~v1
  = du_allValidIdentB'45'sound_58 v0
du_allValidIdentB'45'sound_58 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_allValidIdentB'45'sound_58 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe du_validIdentB'45'sound_50 (coe v1))
             (coe du_allValidIdentB'45'sound_58 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.NameClash.nameElem-false→All≢
d_nameElem'45'false'8594'All'8802'_72 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_nameElem'45'false'8594'All'8802'_72 v0 v1 ~v2
  = du_nameElem'45'false'8594'All'8802'_72 v0 v1
du_nameElem'45'false'8594'All'8802'_72 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_nameElem'45'false'8594'All'8802'_72 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
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
                              seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                       else coe
                              seq (coe v6)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                                 (coe du_nameElem'45'false'8594'All'8802'_72 (coe v0) (coe v3)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.NameClash.namesDistinct-sound
d_namesDistinct'45'sound_110 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_namesDistinct'45'sound_110 v0 ~v1
  = du_namesDistinct'45'sound_110 v0
du_namesDistinct'45'sound_110 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_namesDistinct'45'sound_110 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
             (coe du_nameElem'45'false'8594'All'8802'_72 (coe v1) (coe v2))
             (coe du_namesDistinct'45'sound_110 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.NameClash.allpairs-head
d_allpairs'45'head_126 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_allpairs'45'head_126 ~v0 v1 v2 ~v3 v4
  = du_allpairs'45'head_126 v1 v2 v4
du_allpairs'45'head_126 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_allpairs'45'head_126 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                           (coe du_allpairs'45'head_126 (coe v4) (coe v8) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.NameClash.map-allpairs-own
d_map'45'allpairs'45'own_150 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_map'45'allpairs'45'own_150 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22))
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                           (coe du_allpairs'45'head_126 (coe v4) (coe v7) (coe v12))
                           (d_map'45'allpairs'45'own_150 (coe v4) (coe v8) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.NameClash.DistinctSymbols
d_DistinctSymbols_164 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 -> ()
d_DistinctSymbols_164 = erased
-- Once.Adequacy.NameClash.distinctOrErr-true
d_distinctOrErr'45'true_174 ::
  Bool ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distinctOrErr'45'true_174 = erased
-- Once.Adequacy.NameClash.GuardB
d_GuardB_176 :: [MAlonzo.Code.Once.Parser.T_Entry_132] -> Bool
d_GuardB_176 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe
            MAlonzo.Code.Data.Bool.Base.d__'8743'__24
            (coe
               MAlonzo.Code.Once.Parser.d_namesDistinct_506
               (coe
                  MAlonzo.Code.Once.Parser.d_emittedNames_544
                  (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v0))))
            (coe
               MAlonzo.Code.Once.Parser.d_allValidIdentB_528
               (coe
                  MAlonzo.Code.Once.Parser.d_emittedNames_544
                  (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v0)))))
         (coe
            MAlonzo.Code.Once.Parser.d_namesDistinct_506
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Once.Parser.d_emittedNames_544
                  (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v0)))
               (coe
                  MAlonzo.Code.Data.List.Base.du_map_22
                  (coe (\ v1 -> MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v1)))
                  (coe MAlonzo.Code.Once.Parser.d_polysOf_146 (coe v0))))))
      (coe
         MAlonzo.Code.Once.Parser.d_namesDistinct_506
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe MAlonzo.Code.Once.Parser.d_entryNameOf_554) (coe v0)))
-- Once.Adequacy.NameClash.guard-whole
d_guard'45'whole_184 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_guard'45'whole_184 = erased
-- Once.Adequacy.NameClash.guard-all
d_guard'45'all_218 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_guard'45'all_218 = erased
-- Once.Adequacy.NameClash.guard-entries
d_guard'45'entries_228 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_guard'45'entries_228 ~v0 v1 ~v2 = du_guard'45'entries_228 v1
du_guard'45'entries_228 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_guard'45'entries_228 v0
  = coe
      du_namesDistinct'45'sound_110
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Once.Parser.d_entryNameOf_554) (coe v0))
-- Once.Adequacy.NameClash.guard-true
d_guard'45'true_238 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_guard'45'true_238 = erased
-- Once.Adequacy.NameClash.namesDistinct-++ʳ
d_namesDistinct'45''43''43''691'_248 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_namesDistinct'45''43''43''691'_248 = erased
-- Once.Adequacy.NameClash.guard-polys
d_guard'45'polys_266 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_guard'45'polys_266 ~v0 v1 ~v2 = du_guard'45'polys_266 v1
du_guard'45'polys_266 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_guard'45'polys_266 v0
  = coe
      du_namesDistinct'45'sound_110
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe (\ v1 -> MAlonzo.Code.Once.Parser.d_pfunName_124 (coe v1)))
         (coe MAlonzo.Code.Once.Parser.d_polysOf_146 (coe v0)))
-- Once.Adequacy.NameClash.ce-syms
d_ce'45'syms_282 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ce'45'syms_282 = erased
-- Once.Adequacy.NameClash.ce-syms-fun
d_ce'45'syms'45'fun_296 ::
  Bool ->
  MAlonzo.Code.Once.Compile.T_CScope_378 ->
  MAlonzo.Code.Once.Parser.T_FunInfo_96 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ce'45'syms'45'fun_296 = erased
-- Once.Adequacy.NameClash.program-no-clash
d_program'45'no'45'clash_650 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_program'45'no'45'clash_650 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38 v1
        -> let v2
                 = MAlonzo.Code.Once.Parser.d_guardDistinct_560
                     (coe
                        MAlonzo.Code.Once.Parser.d_extractFunctions'45'go_216
                        (coe MAlonzo.Code.Once.Parser.d_extractAliases_76 (coe v0))
                        (coe v1) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
                  -> coe
                       MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> let v4
                           = MAlonzo.Code.Once.Compile.d_compileEntries_466
                               (coe MAlonzo.Code.Once.IR.C_Heap_8)
                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                               (coe MAlonzo.Code.Once.Compile.d_emptyCScope_394) (coe v3) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
                            -> coe
                                 MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                            -> coe
                                 d_map'45'allpairs'45'own_150
                                 (coe
                                    MAlonzo.Code.Once.Parser.d_emittedNames_544
                                    (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3)))
                                 (coe
                                    du_namesDistinct'45'sound_110
                                    (coe
                                       MAlonzo.Code.Once.Parser.d_emittedNames_544
                                       (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3))))
                                 (coe
                                    du_allValidIdentB'45'sound_58
                                    (coe
                                       MAlonzo.Code.Once.Parser.d_emittedNames_544
                                       (coe MAlonzo.Code.Once.Parser.d_funsOf_138 (coe v3))))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.NameClash._.guard
d_guard_686 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_guard_686 = erased
-- Once.Adequacy.NameClash._.bridge
d_bridge_688 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  [MAlonzo.Code.Once.Compile.T_CompiledFun_238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge_688 = erased
