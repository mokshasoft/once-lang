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

module MAlonzo.Code.Once.Adequacy.LabelSymbols where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.SymbolInjective
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.LabelSymbols.key
d_key_6 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_key_6 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Label.C_once_30 v1
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v1))
      MAlonzo.Code.Once.CCC.Label.C_sigop_32 v1 v2
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe MAlonzo.Code.Once.CCC.Label.d_labelSym_398 (coe v0))
      MAlonzo.Code.Once.CCC.Label.C_callee_34 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 v2
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v2))
             MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 v2
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
                       (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LabelSymbols.DefL
d_DefL_18 a0 = ()
data T_DefL_18 = C_d'45'once_22 | C_d'45'callee_26
-- Once.Adequacy.LabelSymbols.tw
d_tw_28 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_tw_28 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             d_tw'45'dec_32 (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v1) (coe '_'))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LabelSymbols.tw-dec
d_tw'45'dec_32 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_tw'45'dec_32 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             else coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                       (coe d_tw_28 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LabelSymbols.last-seg
d_last'45'seg_46 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_last'45'seg_46 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_reverse_444
      (d_tw_28 (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v0))
-- Once.Adequacy.LabelSymbols.reverse⁺
d_reverse'8314'_54 ::
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()) ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_reverse'8314'_54 ~v0 v1 v2 = du_reverse'8314'_54 v1 v2
du_reverse'8314'_54 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_reverse'8314'_54 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v1
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4 v5
        -> case coe v0 of
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                    (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v7)
                    (coe du_reverse'8314'_54 (coe v7) (coe v5))
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LabelSymbols.tw-split
d_tw'45'split_70 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tw'45'split_70 = erased
-- Once.Adequacy.LabelSymbols._.go
d_go_90 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_90 = erased
-- Once.Adequacy.LabelSymbols.last-seg-split
d_last'45'seg'45'split_102 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_last'45'seg'45'split_102 = erased
-- Once.Adequacy.LabelSymbols._.r≡
d_r'8801'_114 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_r'8801'_114 = erased
-- Once.Adequacy.LabelSymbols.digit≢_
d_digit'8802'__122 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_digit'8802'__122 = erased
-- Once.Adequacy.LabelSymbols.digits-free
d_digits'45'free_134 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_digits'45'free_134 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164 erased
      (coe
         MAlonzo.Code.Data.Nat.Show.du_charsInBase_64 (coe (10 :: Integer))
         (coe v0))
      (coe
         MAlonzo.Code.Once.Target.SymbolInjective.d_charsInBase'45'all'45'digits_164
         (coe v0))
-- Once.Adequacy.LabelSymbols.lid-shape
d_lid'45'shape_144 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lid'45'shape_144 = erased
-- Once.Adequacy.LabelSymbols.idx-of-once
d_idx'45'of'45'once_160 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idx'45'of'45'once_160 = erased
-- Once.Adequacy.LabelSymbols.idx-of-thunk
d_idx'45'of'45'thunk_166 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idx'45'of'45'thunk_166 = erased
-- Once.Adequacy.LabelSymbols.showNat-inj
d_showNat'45'inj_174 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_showNat'45'inj_174 = erased
-- Once.Adequacy.LabelSymbols.head-of
d_head'45'of_182 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_head'45'of_182 v0
  = case coe v0 of
      [] -> coe ' '
      (:) v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LabelSymbols.once-head
d_once'45'head_188 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_once'45'head_188 = erased
-- Once.Adequacy.LabelSymbols.thunk-head
d_thunk'45'head_194 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thunk'45'head_194 = erased
-- Once.Adequacy.LabelSymbols.fn-head
d_fn'45'head_200 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fn'45'head_200 = erased
-- Once.Adequacy.LabelSymbols.cnt≢fn
d_cnt'8802'fn_208 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cnt'8802'fn_208 = erased
-- Once.Adequacy.LabelSymbols.sym-key
d_sym'45'key_232 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  T_DefL_18 ->
  T_DefL_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym'45'key_232 = erased
-- Once.Adequacy.LabelSymbols.keys→syms
d_keys'8594'syms_306 ::
  [MAlonzo.Code.Once.CCC.Label.T_Label_28] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_keys'8594'syms_306 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22)
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v11 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                           (coe du_go_328 (coe v8) (coe v6) (coe v11))
                           (d_keys'8594'syms_306 (coe v8) (coe v6) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.LabelSymbols._.go
d_go_328 ::
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28] ->
  T_DefL_18 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Once.CCC.Label.T_Label_28 ->
  [MAlonzo.Code.Once.CCC.Label.T_Label_28] ->
  T_DefL_18 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_go_328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 v9 v10
  = du_go_328 v7 v9 v10
du_go_328 ::
  [MAlonzo.Code.Once.CCC.Label.T_Label_28] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_go_328 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
        -> coe seq (coe v2) (coe v1)
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (\ v13 -> coe v11 erased)
                           (coe du_go_328 (coe v8) (coe v6) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
