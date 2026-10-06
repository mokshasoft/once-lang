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

module MAlonzo.Code.Once.CCC.Codegen.LabelDefs where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore
import qualified MAlonzo.Code.Once.CanonicalName

-- Once.CCC.Codegen.LabelDefs.Dst
d_Dst_8 :: [Integer] -> ()
d_Dst_8 = erased
-- Once.CCC.Codegen.LabelDefs.Dj
d_Dj_10 :: [Integer] -> [Integer] -> ()
d_Dj_10 = erased
-- Once.CCC.Codegen.LabelDefs.Win
d_Win_20 :: Integer -> Integer -> [Integer] -> ()
d_Win_20 = erased
-- Once.CCC.Codegen.LabelDefs.dj-[]
d_dj'45''91''93'_30 ::
  [Integer] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dj'45''91''93'_30 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
             (d_dj'45''91''93'_30 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelDefs.dj-sym
d_dj'45'sym_38 ::
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dj'45'sym_38 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_266 v1
      (\ v3 v4 ->
         coe
           MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate_266 v0
           (\ v5 v6 v7 ->
              coe
                MAlonzo.Code.Data.List.Relation.Unary.All.du_lookup_436 v1
                (coe
                   MAlonzo.Code.Data.List.Relation.Unary.All.du_lookup_436 v0 v2 v6)
                v4 erased))
-- Once.CCC.Codegen.LabelDefs.dj-++ˡ
d_dj'45''43''43''737'_62 ::
  [Integer] ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dj'45''43''43''737'_62 v0 ~v1 ~v2 = du_dj'45''43''43''737'_62 v0
du_dj'45''43''43''737'_62 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_dj'45''43''43''737'_62 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe v0)
-- Once.CCC.Codegen.LabelDefs.dj-++ʳ
d_dj'45''43''43''691'_70 ::
  [Integer] ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dj'45''43''43''691'_70 v0 v1 ~v2 v3 v4
  = du_dj'45''43''43''691'_70 v0 v1 v3 v4
du_dj'45''43''43''691'_70 ::
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_dj'45''43''43''691'_70 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe seq (coe v3) (coe v2)
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v12 v13
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                              (coe v1) (coe v6) (coe v12))
                           (coe
                              du_dj'45''43''43''691'_70 (coe v9) (coe v1) (coe v7) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelDefs.dst-++
d_dst'45''43''43'_84 ::
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_dst'45''43''43'_84 v0 ~v1 = du_dst'45''43''43'_84 v0
du_dst'45''43''43'_84 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_dst'45''43''43'_84 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Properties.du_'43''43''8314'_74
      (coe v0)
-- Once.CCC.Codegen.LabelDefs.dst-split
d_dst'45'split_90 ::
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_dst'45'split_90 v0 ~v1 v2 = du_dst'45'split_90 v0 v2
du_dst'45'split_90 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_dst'45'split_90 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315''737'_594
                          (coe v3) (coe v6))
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe du_dst'45'split_90 (coe v3) (coe v7))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe du_dst'45'split_90 (coe v3) (coe v7))))
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe
                             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8315''691'_610
                             (coe v3) (coe v6))
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe du_dst'45'split_90 (coe v3) (coe v7))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelDefs.dj-win
d_dj'45'win_124 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_dj'45'win_124 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8
  = du_dj'45'win_124 v4 v5 v6 v7
du_dj'45'win_124 ::
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_dj'45'win_124 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v2
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
        -> case coe v0 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164 erased
                       (coe v1) (coe v3))
                    (coe du_dj'45'win_124 (coe v9) (coe v1) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelDefs.win-weaken
d_win'45'weaken_152 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_win'45'weaken_152 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_win'45'weaken_152 v4 v5 v6
du_win'45'weaken_152 ::
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_win'45'weaken_152 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
      (coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908 (coe v1)
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
              (coe
                 MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)) (coe v2))))
      (coe v0)
-- Once.CCC.Codegen.LabelDefs.fresh-below
d_fresh'45'below_170 ::
  Integer ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fresh'45'below_170 ~v0 ~v1 ~v2 v3 ~v4 = du_fresh'45'below_170 v3
du_fresh'45'below_170 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fresh'45'below_170 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164 erased
      (coe v0)
-- Once.CCC.Codegen.LabelDefs.fresh-above
d_fresh'45'above_188 ::
  Integer ->
  Integer ->
  Integer ->
  [Integer] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_fresh'45'above_188 ~v0 ~v1 ~v2 v3 ~v4 = du_fresh'45'above_188 v3
du_fresh'45'above_188 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_fresh'45'above_188 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164 erased
      (coe v0)
-- Once.CCC.Codegen.LabelDefs.ctrl-clab
d_ctrl'45'clab_196 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_FlatCtrl_2226 ->
  Maybe Integer
d_ctrl'45'clab_196 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'label_2228 v1
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v1))
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'jmp_2230 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'scratch'45'zero_2232 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'branch'45'tag'45'zero_2234 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v3))
             MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'ret_2238 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'call'45'fn_2240 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'start_2242 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelDefs.clab-of
d_clab'45'of_202 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  Maybe Integer
d_clab'45'of_202 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v2
           -> coe d_ctrl'45'clab_196 (coe v2)
         _ -> coe v1)
-- Once.CCC.Codegen.LabelDefs.cl-at
d_cl'45'at_206 :: Maybe Integer -> [Integer] -> [Integer]
d_cl'45'at_206 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelDefs.clabs
d_clabs_214 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [Integer]
d_clabs_214 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             d_cl'45'at_206 (coe d_clab'45'of_202 (coe v1))
             (coe d_clabs_214 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelDefs.clabs-++
d_clabs'45''43''43'_224 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_clabs'45''43''43'_224 = erased
-- Once.CCC.Codegen.LabelDefs._.go
d_go_240 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  Maybe Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_240 = erased
-- Once.CCC.Codegen.LabelDefs.fdef-of
d_fdef'45'of_246 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4]
d_fdef'45'of_246 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.CCC.Machine.SMCore.C_instr'45'ctrl_2318 v2
           -> case coe v2 of
                MAlonzo.Code.Once.CCC.Machine.SMCore.C_c'45'entry_2236 v3 v4
                  -> case coe v3 of
                       MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.CCC.Codegen.LabelDefs.fdefs
d_fdefs_250 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4]
d_fdefs_250 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_fdef'45'of_246 (coe v1)) (coe d_fdefs_250 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Codegen.LabelDefs.NoFn
d_NoFn_256 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] -> ()
d_NoFn_256 = erased
-- Once.CCC.Codegen.LabelDefs.nf
d_nf_264 ::
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nf_264 = erased
-- Once.CCC.Codegen.LabelDefs._.go
d_go_288 ::
  MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2250] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_288 = erased
