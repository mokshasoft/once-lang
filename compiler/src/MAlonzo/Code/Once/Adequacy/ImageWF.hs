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

module MAlonzo.Code.Once.Adequacy.ImageWF where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Arith.Machine.IR
import qualified MAlonzo.Code.Once.Arith.SigOp.Block
import qualified MAlonzo.Code.Once.CCC.Codegen.ImageSymbols
import qualified MAlonzo.Code.Once.Compile
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.ImageWF.block-symbol
d_block'45'symbol_6 ::
  MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_block'45'symbol_6 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'own_56
      (coe
         MAlonzo.Code.Once.Arith.SigOp.Block.du_block'45'name_366
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'shape_174 (coe v0))
         (coe
            MAlonzo.Code.Once.Arith.Machine.IR.d_block'45'body_178 (coe v0)))
-- Once.Adequacy.ImageWF.block-syms
d_block'45'syms_10 ::
  [MAlonzo.Code.Once.Arith.Machine.IR.T_ArithBlock_166] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_block'45'syms_10 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe (\ v1 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))
      (coe
         MAlonzo.Code.Once.Compile.d_dedup'45'blocks_952
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe
               (\ v1 ->
                  coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_block'45'symbol_6 (coe v1)) (coe v1)))
            (coe v0)))
-- Once.Adequacy.ImageWF.prog-defs
d_prog'45'defs_16 ::
  MAlonzo.Code.Once.Denotation.Program.T_IRProgram_380 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_prog'45'defs_16 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_heap'45'symbol_8)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe ("_start" :: Data.Text.Text))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
               (coe MAlonzo.Code.Once.Compile.d_image'45'of_954 (coe v0)))
            (coe
               d_block'45'syms_10
               (coe MAlonzo.Code.Once.Compile.d_program'45'blocks_900 (coe v0)))))
-- Once.Adequacy.ImageWF.lib-defs
d_lib'45'defs_20 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lib'45'defs_20 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_heap'45'symbol_8)
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.CCC.Codegen.ImageSymbols.d_adefs_38
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'image_1004
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0))))
         (coe
            d_block'45'syms_10
            (coe
               MAlonzo.Code.Once.Compile.d_lib'45'blocks_1008
               (coe MAlonzo.Code.Once.Compile.d_moduleTable_870 (coe v0)))))
-- Once.Adequacy.ImageWF.Resolved
d_Resolved_24 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d_Resolved_24 = erased
-- Once.Adequacy.ImageWF.ProgG
d_ProgG_34 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_ProgG_34 = erased
-- Once.Adequacy.ImageWF.ProgP
d_ProgP_46 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 -> ()
d_ProgP_46 = erased
-- Once.Adequacy.ImageWF.prog-unique
d_prog'45'unique_58
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ImageWF.prog-unique"
-- Once.Adequacy.ImageWF.prog-sigops
d_prog'45'sigops_66
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ImageWF.prog-sigops"
-- Once.Adequacy.ImageWF.lib-unique
d_lib'45'unique_70
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ImageWF.lib-unique"
-- Once.Adequacy.ImageWF.lib-resolved
d_lib'45'resolved_74
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.ImageWF.lib-resolved"
