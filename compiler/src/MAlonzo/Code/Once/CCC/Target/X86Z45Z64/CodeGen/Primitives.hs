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

module MAlonzo.Code.Once.CCC.Target.X86Z45Z64.CodeGen.Primitives where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Type

-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp
d_compile'45'sigOp_12 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_compile'45'sigOp_12 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_call'45'sym_84
         (coe
            MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
            (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp-size
d_compile'45'sigOp'45'size_16 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> Integer
d_compile'45'sigOp'45'size_16 ~v0 = du_compile'45'sigOp'45'size_16
du_compile'45'sigOp'45'size_16 :: Integer
du_compile'45'sigOp'45'size_16 = coe (1 :: Integer)
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-sigOp-length
d_compile'45'sigOp'45'length_20 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'sigOp'45'length_20 = erased
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-const
d_compile'45'const_24 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
d_compile'45'const_24 ~v0 v1 v2 = du_compile'45'const_24 v1 v2
du_compile'45'const_24 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny ->
  [MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.T_Instr_62]
du_compile'45'const_24 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_fits'45'int_198
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe
                MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_mov_64
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_reg_56
                   (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_rax_12))
                (coe
                   MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_imm_60 (coe v1)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Type.C_fits'45'float_200
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Once.CCC.Target.X86Z45Z64.Syntax.C_ud2_94)
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-const-size
d_compile'45'const'45'size_30 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Integer
d_compile'45'const'45'size_30 ~v0 v1
  = du_compile'45'const'45'size_30 v1
du_compile'45'const'45'size_30 ::
  MAlonzo.Code.Once.Type.T_FitsInReg_196 -> Integer
du_compile'45'const'45'size_30 v0
  = coe seq (coe v0) (coe (1 :: Integer))
-- Once.CCC.Target.X86-64.CodeGen.Primitives.compile-const-length
d_compile'45'const'45'length_38 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_FitsInReg_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compile'45'const'45'length_38 = erased
