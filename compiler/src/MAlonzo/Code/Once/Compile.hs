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

module MAlonzo.Code.Once.Compile where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Once.Escape
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Optimize
import qualified MAlonzo.Code.Once.Surface.Desugar
import qualified MAlonzo.Code.Once.Surface.IR
import qualified MAlonzo.Code.Once.Type

-- Once.Compile.compile
d_compile_8 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_10
d_compile_8 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Escape.d_escape_126 v0 v1
      (coe
         MAlonzo.Code.Once.Optimize.d_optimize_1386 v0 v1
         (MAlonzo.Code.Once.Surface.Desugar.d_desugar_16
            (coe v0) (coe v1) (coe v2)))
-- Once.Compile.compile-no-escape
d_compile'45'no'45'escape_16 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_10
d_compile'45'no'45'escape_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Optimize.d_optimize_1386 v0 v1
      (MAlonzo.Code.Once.Surface.Desugar.d_desugar_16
         (coe v0) (coe v1) (coe v2))
-- Once.Compile.compile-no-opt
d_compile'45'no'45'opt_24 ::
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Type.T_Type_32 ->
  MAlonzo.Code.Once.Surface.IR.T_SurfaceIR_6 ->
  MAlonzo.Code.Once.IR.T_IR_10
d_compile'45'no'45'opt_24 v0 v1
  = coe
      MAlonzo.Code.Once.Surface.Desugar.d_desugar_16 (coe v0) (coe v1)
