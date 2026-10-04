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

module MAlonzo.Code.Once.CCC.Codegen.BlockLayout where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.CCC.Codegen.BlockLayout.Layout._.fetch
d_fetch_18 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
d_fetch_18 ~v0 = du_fetch_18
du_fetch_18 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  Maybe MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238
du_fetch_18 = coe MAlonzo.Code.Once.CCC.Machine.Flat.du_fetch_246
-- Once.CCC.Codegen.BlockLayout.Layout._.find-thunk
d_find'45'thunk_20 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Maybe Integer
d_find'45'thunk_20 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_find'45'thunk_234 (coe v0)
-- Once.CCC.Codegen.BlockLayout.Layout._.ft-at
d_ft'45'at_22 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'at_22 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'at_194 (coe v0)
-- Once.CCC.Codegen.BlockLayout.Layout._.ft-go
d_ft'45'go_24 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'go_24 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_192 (coe v0)
-- Once.CCC.Codegen.BlockLayout.Layout._.ft-match
d_ft'45'match_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  Integer -> Maybe Integer
d_ft'45'match_28 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_196 (coe v0)
-- Once.CCC.Codegen.BlockLayout.Layout.Span
d_Span_32 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_Span_32 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.fetch-skip
d_fetch'45'skip_50 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fetch'45'skip_50 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.span-head
d_span'45'head_68 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_span'45'head_68 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.span-shift
d_span'45'shift_104 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_span'45'shift_104 = erased
-- Once.CCC.Codegen.BlockLayout.Layout._.+-assoc-lemma
d_'43''45'assoc'45'lemma_132 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc'45'lemma_132 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.blocks-placed
d_blocks'45'placed_152 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'placed_152 ~v0 v1 = du_blocks'45'placed_152 v1
du_blocks'45'placed_152 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_blocks'45'placed_152 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                erased)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                (coe
                   (\ v3 v4 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe
                           addInt
                           (coe
                              MAlonzo.Code.Data.List.Base.du_length_268
                              (MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'layout_2330
                                 (coe v1)))
                           (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                        erased))
                (coe v2) (coe du_blocks'45'placed_152 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.BlockLayout.Layout.blocks-placed-linked
d_blocks'45'placed'45'linked_176 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'placed'45'linked_176 ~v0 v1 v2
  = du_blocks'45'placed'45'linked_176 v1 v2
du_blocks'45'placed'45'linked_176 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_blocks'45'placed'45'linked_176 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 addInt (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
              erased))
      (coe v1) (coe du_blocks'45'placed_152 (coe v1))
-- Once.CCC.Codegen.BlockLayout.Layout.ft-hit
d_ft'45'hit_198 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ft'45'hit_198 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.block-resolves
d_block'45'resolves_222 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  Integer ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_block'45'resolves_222 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.MissBefore
d_MissBefore_236 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_MissBefore_236 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.blocks-at
d_blocks'45'at_254 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_blocks'45'at_254 ~v0 v1 v2 v3 = du_blocks'45'at_254 v1 v2 v3
du_blocks'45'at_254 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_blocks'45'at_254 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v6)
                    (case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                                 (coe
                                    (\ v9 v10 ->
                                       coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe v10)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                  (coe v10))))))
                                 (coe v4)
                                 (coe
                                    du_blocks'45'at_254
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.CCC.Machine.SMCore.d_block'45'layout_2330
                                          (coe v3)))
                                    (coe v4) (coe v8)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.BlockLayout.Layout.NoThunk
d_NoThunk_286 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] -> ()
d_NoThunk_286 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.no-thunk-miss
d_no'45'thunk'45'miss_298 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'thunk'45'miss_298 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.no-thunk-at
d_no'45'thunk'45'at_308 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Maybe MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'thunk'45'at_308 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.no-thunk-match
d_no'45'thunk'45'match_320 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_no'45'thunk'45'match_320 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.NoThunks
d_NoThunks_386 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_NoThunks_386 = erased
-- Once.CCC.Codegen.BlockLayout.Layout.missBefore-from
d_missBefore'45'from_400 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2238] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
d_missBefore'45'from_400 ~v0 ~v1 v2 v3
  = du_missBefore'45'from_400 v2 v3
du_missBefore'45'from_400 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_missBefore'45'from_400 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe du_missBefore'45'from_400 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
