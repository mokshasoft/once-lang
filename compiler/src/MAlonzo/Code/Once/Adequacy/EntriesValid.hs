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

module MAlonzo.Code.Once.Adequacy.EntriesValid where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Parser.Module.Core

-- Once.Adequacy.EntriesValid.MonoValid
d_MonoValid_6 :: MAlonzo.Code.Once.Parser.T_Entry_132 -> ()
d_MonoValid_6 = erased
-- Once.Adequacy.EntriesValid.valid-of
d_valid'45'of_14 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_valid'45'of_14 v0 ~v1 = du_valid'45'of_14 v0
du_valid'45'of_14 ::
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_valid'45'of_14 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Parser.C_e'45'fun_134 v3
               -> let v4
                        = MAlonzo.Code.Once.Parser.d_funIsPrimitive_112 (coe v3) in
                  coe
                    (coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                          (coe du_valid'45'of_14 (coe v2))))
             MAlonzo.Code.Once.Parser.C_e'45'poly_136 v3
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe du_valid'45'of_14 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.EntriesValid.valid-mod
d_valid'45'mod_56 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_valid'45'mod_56 v0 v1 ~v2 = du_valid'45'mod_56 v0 v1
du_valid'45'mod_56 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Once.Parser.T_Entry_132] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_valid'45'mod_56 v0 v1
  = coe seq (coe v0) (coe du_valid'45'of_14 (coe v1))
-- Once.Adequacy.EntriesValid.cont-dot
d_cont'45'dot_68 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cont'45'dot_68 = erased
-- Once.Adequacy.EntriesValid.chars-dot
d_chars'45'dot_84 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_chars'45'dot_84 = erased
-- Once.Adequacy.EntriesValid.dot-invalid
d_dot'45'invalid_100 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dot'45'invalid_100 = erased
