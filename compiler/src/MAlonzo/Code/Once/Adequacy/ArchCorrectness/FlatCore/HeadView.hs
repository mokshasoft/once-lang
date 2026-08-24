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

module MAlonzo.Code.Once.Adequacy.ArchCorrectness.FlatCore.HeadView where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Once.CCC.FrameSemantics
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CCC.Machine.Flat
import qualified MAlonzo.Code.Once.CCC.Machine.SMCore

-- Once.Adequacy.ArchCorrectness.FlatCore.HeadView._.fl-go
d_fl'45'go_22 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   [AgdaAny]) ->
  (AgdaAny -> Bool) ->
  (MAlonzo.Code.Once.CCC.Label.T_Label_22 -> AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'go_22 v0 ~v1 ~v2 ~v3 ~v4 = du_fl'45'go_22 v0
du_fl'45'go_22 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'go_22 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'go_126 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.HeadView._.fl-label-match
d_fl'45'label'45'match_24 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   [AgdaAny]) ->
  (AgdaAny -> Bool) ->
  (MAlonzo.Code.Once.CCC.Label.T_Label_22 -> AgdaAny) ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_fl'45'label'45'match_24 v0 ~v1 ~v2 ~v3 ~v4
  = du_fl'45'label'45'match_24 v0
du_fl'45'label'45'match_24 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_fl'45'label'45'match_24 v0
  = coe
      MAlonzo.Code.Once.CCC.Machine.Flat.d_fl'45'label'45'match_130
      (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.HeadView._.ft-go
d_ft'45'go_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   [AgdaAny]) ->
  (AgdaAny -> Bool) ->
  (MAlonzo.Code.Once.CCC.Label.T_Label_22 -> AgdaAny) ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'go_26 v0 ~v1 ~v2 ~v3 ~v4 = du_ft'45'go_26 v0
du_ft'45'go_26 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_ft'45'go_26 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'go_172 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.HeadView._.ft-match
d_ft'45'match_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   [AgdaAny]) ->
  (AgdaAny -> Bool) ->
  (MAlonzo.Code.Once.CCC.Label.T_Label_22 -> AgdaAny) ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
d_ft'45'match_28 v0 ~v1 ~v2 ~v3 ~v4 = du_ft'45'match_28 v0
du_ft'45'match_28 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  Bool ->
  [MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218] ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> Integer -> Maybe Integer
du_ft'45'match_28 v0
  = coe MAlonzo.Code.Once.CCC.Machine.Flat.d_ft'45'match_176 (coe v0)
-- Once.Adequacy.ArchCorrectness.FlatCore.HeadView.has-label
d_has'45'label_30 ::
  MAlonzo.Code.Once.CCC.FrameSemantics.T_FrameSemantics_6 ->
  () ->
  (MAlonzo.Code.Once.CCC.Machine.SMCore.T_AbstractInstr_2218 ->
   [AgdaAny]) ->
  (AgdaAny -> Bool) ->
  (MAlonzo.Code.Once.CCC.Label.T_Label_22 -> AgdaAny) ->
  [AgdaAny] -> Bool
d_has'45'label_30 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_has'45'label_30 v3 v5
du_has'45'label_30 :: (AgdaAny -> Bool) -> [AgdaAny] -> Bool
du_has'45'label_30 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      (:) v2 v3
        -> let v4 = coe v0 v2 in
           coe
             (if coe v4
                then coe v4
                else coe du_has'45'label_30 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ArchCorrectness.FlatCore.HeadView.HeadView
d_HeadView_50 a0 a1 a2 a3 a4 a5 = ()
data T_HeadView_50
  = C_hv'45'clabel_68 MAlonzo.Code.Once.CCC.Label.T_LabelId_6 |
    C_hv'45'plain_82 |
    C_hv'45'otherlabel_100 MAlonzo.Code.Once.CCC.Label.T_LabelId_6
                           [AgdaAny]
